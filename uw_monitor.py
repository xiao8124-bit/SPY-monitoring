# -*- coding: utf-8 -*-
"""
SPY 期权结构 + 资金流 实时监控（Unusual Whales API）→ Telegram
====================================================================

三种运行模式（由环境变量 MODE 控制，Actions 页面 Run workflow 时可选择）：
  monitor        正式监控：美股常规时段内每 15 秒轮询一次，维护"实时面板"（同一条 Telegram 消息原地刷新、静音）；
                 只在"共振"（结构/动量/资金流 ≥2 类同向）或关键结构事件、巨额单时才推送带提示音的消息；15:55 ET 发收盘摘要。
  probe          接口探测：逐个调用 UW 接口，把状态码、字段结构、解析结果和大单频率统计发到 Telegram（首次部署用）。
  telegram-test  推送测试：发一条消息再编辑它，验证 Bot 与"原地刷新"功能。

信号三类（同向 ≥2 类才算"共振"）：
  结构   价格"确认"穿过 Flip 区（持续 60 秒）/ 确认突破 Call Wall、Put Wall（持续 45 秒）；
         Flip 迁移、墙位同向移动只作为辅助证据
  动量   快速异动（20 分钟内幅度，阈值随当日波动自适应）/ 破位后继续延伸（每 0.2%）/ 价格里程碑
  资金流 近 10 分钟净权利金（call 净 − put 净）异常偏离（z 分数）、同向大单合计、单笔巨额单

防噪音：Flip 用"区间 + 随波动自适应的缓冲 + 持续确认"，来回震荡时自动降级；共振有冷却时间；
同一波行情只在升级或明显延续时才再次提醒；"新信号"和"延续/升级提醒"各有每日带提示音上限（超出自动转静音）。
常用阈值（uw_monitor.yml 里列出的那些）可在 GitHub 仓库 Settings → Secrets and variables → Actions → Variables 里
新建同名变量来调整；其余阈值也都读同名环境变量，在 uw_monitor.yml 的 env 里照样子加一行即可。
本脚本与旧的 FlashAlpha 版完全独立：文件名、工作流、状态文件（uw_state.json）都不同，互不影响。

注意：本脚本不会在日志里打印任何密钥；Telegram / UW 的报错信息会先做脱敏。
仅为描述性提示，不构成任何交易建议。
"""
from __future__ import annotations

import json
import math
import os
import re
import statistics
import sys
import time
import traceback
from datetime import date, datetime, time as dtime, timedelta, timezone
from zoneinfo import ZoneInfo

import requests

ET = ZoneInfo("America/New_York")
UTC = timezone.utc
UW_BASE = "https://api.unusualwhales.com"
TG_BASE = "https://api.telegram.org"
STATE_VERSION = 3
STATE_FILE = os.environ.get("STATE_FILE", "uw_state.json")
DISCLAIMER = "⚠ 描述性提示，非交易建议"
SRC_LABEL = {"oi": "OI口径", "vol": "成交口径"}

# ----------------------------------------------------------------------------
# 脱敏与日志
# ----------------------------------------------------------------------------
SECRETS: list = []


def safe(text) -> str:
    s = str(text)
    for sec in SECRETS:
        if sec and len(sec) >= 6:
            s = s.replace(sec, "***")
    return s


def log(*args) -> None:
    print(safe(" ".join(str(a) for a in args)), flush=True)


# ----------------------------------------------------------------------------
# 配置
# ----------------------------------------------------------------------------
class Cfg:
    def __init__(self, overrides: dict | None = None):
        ov = overrides or {}

        def raw(name):
            if name in ov:
                return str(ov[name]).strip()
            return os.environ.get(name, "").strip()

        def s(name, default=""):
            v = raw(name)
            return v if v else default

        def f(name, default):
            v = raw(name)
            try:
                return float(v) if v else float(default)
            except ValueError:
                return float(default)

        def b(name, default=False):
            v = raw(name).lower()
            return (v in ("1", "true", "yes", "y", "on")) if v else default

        self.symbol = s("SYMBOL", "SPY").upper()
        self.mode = s("MODE", "monitor").lower()
        self.force_run = b("FORCE_RUN")
        self.debug = b("DEBUG")
        self.uw_key = s("UW_API_KEY")
        self.tg_token = s("TELEGRAM_BOT_TOKEN")
        self.tg_chat = s("TELEGRAM_CHAT_ID")

        # 运行节奏
        self.poll = f("POLL_INTERVAL_SECONDS", 15)
        self.loop_s = f("LOOP_DURATION_SECONDS", 870)
        self.win_start = s("WINDOW_START", "09:30")
        self.win_end = s("WINDOW_END", "16:00")
        self.close_digest_at = s("CLOSE_DIGEST_AT", "15:55")
        self.levels_every = f("LEVELS_EVERY_SECONDS", 30)
        self.ticks_every = f("TICKS_EVERY_SECONDS", 30)
        self.flow_every = f("FLOW_EVERY_SECONDS", 30)
        self.panel_every = f("PANEL_UPDATE_SECONDS", 30)

        # 点位口径
        self.primary_src = s("PRIMARY_SOURCE", "oi").lower()
        self.live_src = s("LIVE_SOURCE", "vol").lower()

        # 结构信号
        self.flip_buffer = f("FLIP_BUFFER", 0.20)             # Flip 区缓冲下限（美元）；实际会随波动自动放大
        self.buffer_vol_mult = f("FLIP_BUFFER_VOL_MULT", 0.6)
        self.chop_window_min = f("CHOP_WINDOW_MIN", 90)       # 90 分钟内第 3 次穿越 Flip 视为"来回震荡"
        self.chop_crosses = int(f("CHOP_CROSSES", 3))
        self.chop_clear_pct = f("CHOP_CLEAR_PCT", 0.25)
        self.zone_radius = f("FLIP_ZONE_RADIUS", 1.5)
        self.flip_confirm_s = f("FLIP_CONFIRM_SECONDS", 60)
        self.wall_buffer = f("WALL_BUFFER", 0.10)
        self.wall_confirm_s = f("WALL_CONFIRM_SECONDS", 45)
        self.flip_migrate = f("FLIP_MIGRATE", 1.0)
        self.wall_shift = f("WALL_SHIFT", 2.0)
        self.migrate_window_min = f("MIGRATE_WINDOW_MIN", 30)
        self.struct_fresh_min = f("STRUCT_FRESH_MIN", 180)

        # 动量：快速异动（impulse）+ 破位后延伸（continuation）；里程碑（milestone）只用于面板/可选的单独推送
        self.impulse_pct = f("IMPULSE_PCT", 0.30)             # 快速异动的最小幅度（下限）
        self.impulse_sigma = f("IMPULSE_SIGMA", 2.0)          # 且需超过 2 倍近期波动（随行情自适应）
        self.impulse_min = f("IMPULSE_MINUTES", 20)
        self.cont_pct = f("CONTINUATION_PCT", 0.20)
        self.cont_step = f("CONTINUATION_STEP_PCT", 0.20)
        self.momentum_pct = f("MOMENTUM_PCT", 0.20)

        # 资金流
        self.tide_window_min = f("TIDE_WINDOW_MIN", 10)
        self.tide_z = f("TIDE_Z", 3.0)              # 纯噪音下约每天 0.5~1 次误触发；单独出现不会推送
        self.tide_abs_min = f("TIDE_ABS_MIN", 1000000)
        self.tide_min_ticks = int(f("TIDE_MIN_TICKS", 45))
        self.print_min = f("PRINT_MIN_PREMIUM", 250000)
        self.print_burst = f("PRINT_BURST_PREMIUM", 3000000)
        self.print_min_count = int(f("PRINT_MIN_COUNT", 3))
        self.print_dominance = f("PRINT_DOMINANCE", 3.0)
        self.print_window_min = f("PRINT_WINDOW_MIN", 10)
        self.mega_min = f("MEGA_PRINT_PREMIUM", 5000000)

        # 共振与推送
        self.conf_window_min = f("CONFLUENCE_WINDOW_MIN", 20)
        self.conf_cooldown_min = f("CONFLUENCE_COOLDOWN_MIN", 20)
        self.repush_min = f("REPUSH_MIN", 20)
        self.repush_pct = f("REPUSH_PROGRESS_PCT", 0.15)
        self.run_retrace_pct = f("RUN_RETRACE_PCT", 0.25)
        self.push_single = s("PUSH_SINGLE", "structure").lower()  # none | structure | all
        self.single_cooldown_min = f("SINGLE_COOLDOWN_MIN", 15)
        self.mega_cooldown_min = f("MEGA_COOLDOWN_MIN", 5)
        self.daily_cap = int(f("DAILY_PUSH_CAP", 6))               # 新信号/单一事件/巨额单：每日带提示音上限
        self.run_cap = int(f("RUN_PUSH_CAP", 6))                   # 已有信号的“延续/升级”提醒：单独的每日上限      # 每天带提示音的信号推送上限，超过后自动转静音

        # 数据健康
        self.stale_price_s = f("STALE_PRICE_SECONDS", 90)
        self.outage_s = f("OUTAGE_SECONDS", 180)


# ----------------------------------------------------------------------------
# 小工具
# ----------------------------------------------------------------------------
def now_et() -> datetime:
    return datetime.now(ET)


def iso(dt: datetime) -> str:
    return dt.astimezone(UTC).strftime("%Y-%m-%dT%H:%M:%SZ")


def parse_iso(s):
    if not s or not isinstance(s, str):
        return None
    try:
        dt = datetime.fromisoformat(s.strip().replace("Z", "+00:00"))
    except ValueError:
        return None
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=UTC)
    return dt


def hm(dt, secs: bool = False) -> str:
    if dt is None:
        return "n/a"
    return dt.astimezone(ET).strftime("%H:%M:%S" if secs else "%H:%M")


def parse_hhmm(s: str) -> dtime:
    h, m = s.split(":")
    return dtime(int(h), int(m))


def num(x):
    """把 str / int / float 安全转成 float；None/空串/非数返回 None。"""
    if x is None or isinstance(x, bool):
        return None
    if isinstance(x, (int, float)):
        return float(x) if math.isfinite(x) else None
    if isinstance(x, str):
        t = x.strip().replace(",", "")
        if not t:
            return None
        try:
            v = float(t)
        except ValueError:
            return None
        return v if math.isfinite(v) else None
    return None


def unwrap(obj):
    """剥掉 {"data": ...} 外壳（最多两层，兼容 data / data.data 两种返回形式）。"""
    for _ in range(2):
        if isinstance(obj, dict) and "data" in obj and isinstance(obj["data"], (dict, list)):
            obj = obj["data"]
        else:
            break
    return obj


def sgn(x) -> int:
    return 1 if x > 0 else (-1 if x < 0 else 0)


def pct_change(new, old):
    if new is None or not old:
        return 0.0
    return (new - old) / old * 100.0


def money(x, signed: bool = False) -> str:
    if x is None:
        return "n/a"
    a = abs(x)
    if a >= 1e9:
        body = f"{a / 1e9:.2f}B"
    elif a >= 1e6:
        body = f"{a / 1e6:.1f}M"
    elif a >= 1e3:
        body = f"{a / 1e3:.0f}K"
    else:
        body = f"{a:.0f}"
    if signed:
        sign = "+" if x > 0 else ("−" if x < 0 else "")
    else:
        sign = "−" if x < 0 else ""
    return f"{sign}${body}"


def fpx(x) -> str:
    return "n/a" if x is None else f"{x:.2f}"


def fsd(x) -> str:
    return "n/a" if x is None else f"{x:+.2f}"


def clip(text: str, n: int = 3900) -> str:
    return text if len(text) <= n else text[: n - 1] + "…"


def dir_label(d) -> str:
    return "▲偏多" if d == "up" else "▼偏空"


def prev_weekdays(today: date, n: int = 5) -> list:
    out, d = [], today
    while len(out) < n:
        d -= timedelta(days=1)
        if d.weekday() < 5:
            out.append(d)
    return out


def in_window(now: datetime, cfg: Cfg) -> bool:
    t = now.astimezone(ET)
    if t.weekday() >= 5:
        return False
    return parse_hhmm(cfg.win_start) <= t.time() < parse_hhmm(cfg.win_end)


def hmd(dt) -> str:
    """带星期和日期的 ET 时间（探测报告用，避免周末看到旧数据时误会）。"""
    if dt is None:
        return "n/a"
    return dt.astimezone(ET).strftime("%a %m-%d %H:%M:%S")


def fmt_age(seconds) -> str:
    if seconds is None:
        return "n/a"
    s = abs(seconds)
    if s < 120:
        return f"{s:.0f}秒"
    if s < 7200:
        return f"{s / 60:.0f}分钟"
    if s < 172800:
        return f"{s / 3600:.1f}小时"
    return f"{s / 86400:.1f}天"


# ----------------------------------------------------------------------------
# HTTP 客户端：UW / Telegram
# ----------------------------------------------------------------------------
class Resp:
    __slots__ = ("ok", "status", "data", "err", "code", "ms")

    def __init__(self, ok, status, data=None, err=None, code=None, ms=0):
        self.ok, self.status, self.data, self.err, self.code, self.ms = ok, status, data, err, code, ms


def _extract_err(r) -> tuple:
    code, msg = None, None
    try:
        j = r.json()
    except ValueError:
        j = None
    if isinstance(j, dict):
        code = j.get("code")
        e = j.get("error")
        if isinstance(e, dict):
            code = code or e.get("code")
            msg = e.get("message")
        elif isinstance(e, str):
            msg = e
        msg = msg or j.get("message") or j.get("msg")
        if j.get("reason") and code:
            code = f"{code}/{j.get('reason')}"
    if msg is None:
        msg = (r.text or "")[:120]
    return (str(code) if code else None), safe(str(msg))[:160]


class UW:
    def __init__(self, key: str, session=None, sleep=time.sleep):
        self.s = session or requests.Session()
        self.s.headers.update({"Authorization": f"Bearer {key}", "Accept": "application/json"})
        self.sleep = sleep
        self.calls = 0
        self.errors = 0
        self.limits: dict = {}          # 最近一次响应里的额度头（Basic 套餐通常没有）

    def get(self, path: str, params: dict | None = None, retries: int = 2, timeout=(5, 20)) -> Resp:
        url = UW_BASE + path
        last = Resp(False, 0, None, "no_attempt", "none", 0)
        for attempt in range(retries + 1):
            t0 = time.monotonic()
            try:
                r = self.s.get(url, params=params, timeout=timeout)
            except requests.RequestException as e:
                ms = int((time.monotonic() - t0) * 1000)
                last = Resp(False, 0, None, f"network:{type(e).__name__}", "network", ms)
                self.errors += 1
                self.sleep(0.8 * (attempt + 1))
                continue
            ms = int((time.monotonic() - t0) * 1000)
            self.calls += 1
            hdrs = getattr(r, "headers", None) or {}
            lim, cnt = hdrs.get("x-uw-token-req-limit"), hdrs.get("x-uw-daily-req-count")
            if lim is not None or cnt is not None:
                self.limits = {"limit": lim, "count": cnt}
            if r.status_code == 200:
                try:
                    return Resp(True, 200, r.json(), None, None, ms)
                except ValueError:
                    return Resp(False, 200, None, "invalid_json", "bad_json", ms)
            code, msg = _extract_err(r)
            last = Resp(False, r.status_code, None, f"{code or ''} {msg}".strip(), code, ms)
            self.errors += 1
            if r.status_code == 429 and code and "daily_request_limit_hit" in code:
                return last                      # 当日额度用完：重试没有意义
            if r.status_code == 429 or r.status_code >= 500:
                ra = num(r.headers.get("Retry-After")) if hasattr(r, "headers") else None
                self.sleep(min(ra if ra else 1.5 * (attempt + 1), 6.0))
                continue
            return last
        return last


class Telegram:
    def __init__(self, token: str, chat_id: str, session=None, sleep=time.sleep):
        self.token, self.chat = token, chat_id
        self.s = session or requests.Session()
        self.sleep = sleep
        self.last_error = None

    def _call(self, method: str, payload: dict):
        url = f"{TG_BASE}/bot{self.token}/{method}"
        err = "unknown"
        for attempt in range(3):
            try:
                r = self.s.post(url, json=payload, timeout=(5, 15))
            except requests.RequestException as e:
                err = f"network:{type(e).__name__}"
                self.sleep(1.0 * (attempt + 1))
                continue
            try:
                j = r.json()
            except ValueError:
                j = {}
            if r.status_code == 200 and j.get("ok"):
                return True, j.get("result"), None
            err = safe(f"{r.status_code} {j.get('description', '')}")[:200]
            if r.status_code == 429:
                ra = num((j.get("parameters") or {}).get("retry_after")) or 2.0
                self.sleep(min(ra, 10.0))
                continue
            return False, None, err
        return False, None, err

    def send(self, text: str, silent: bool = False):
        ok, res, err = self._call(
            "sendMessage",
            {"chat_id": self.chat, "text": clip(text), "disable_notification": bool(silent),
             "disable_web_page_preview": True},
        )
        if ok and isinstance(res, dict):
            self.last_error = None
            return res.get("message_id")
        self.last_error = err
        return None

    def edit(self, message_id, text: str) -> str:
        ok, _res, err = self._call(
            "editMessageText",
            {"chat_id": self.chat, "message_id": message_id, "text": clip(text),
             "disable_web_page_preview": True},
        )
        if ok:
            return "ok"
        el = (err or "").lower()
        if "not modified" in el:
            return "ok"
        if "message to edit not found" in el or "message_id_invalid" in el or "can't be edited" in el:
            return "gone"
        self.last_error = err
        return "err"


# ----------------------------------------------------------------------------
# 数据解析（对字段缺失/类型不一致保持宽容）
# ----------------------------------------------------------------------------
def _ts_from_ms(v):
    x = num(v)
    if x is None or x <= 0:
        return None
    if x < 1e11:  # 秒
        x *= 1000.0
    return datetime.fromtimestamp(x / 1000.0, UTC)


def parse_quote(raw):
    d = unwrap(raw)
    if not isinstance(d, dict):
        return None
    lt = d.get("last_trade") if isinstance(d.get("last_trade"), dict) else {}
    q = d.get("quote") if isinstance(d.get("quote"), dict) else {}
    qv = d.get("quote_values") if isinstance(d.get("quote_values"), dict) else {}
    bid = num((q.get("bid") or {}).get("price")) if isinstance(q.get("bid"), dict) else None
    ask = num((q.get("ask") or {}).get("price")) if isinstance(q.get("ask"), dict) else None
    mid = num(qv.get("midpoint"))
    if mid is None and bid is not None and ask is not None:
        mid = (bid + ask) / 2.0
    last = num(lt.get("price"))
    price = last if last is not None else mid
    ts = _ts_from_ms(lt.get("time")) if last is not None else None
    if ts is None:
        ts = _ts_from_ms(q.get("time"))
    if price is None:
        return None
    return {"price": price, "mid": mid, "bid": bid, "ask": ask, "ts": ts,
            "quote_age_ms": num(qv.get("quote_age_ms")), "market_time": d.get("market_time"),
            "src": "quote"}


def parse_stock_state(raw):
    """备用价格源（/stock-state），字段名按常见形式宽容解析。"""
    d = unwrap(raw)
    if isinstance(d, list) and d:
        d = d[-1]
    if not isinstance(d, dict):
        return None
    price = None
    for k in ("close", "last", "price", "last_price"):
        price = num(d.get(k))
        if price is not None:
            break
    if price is None:
        return None
    ts = parse_iso(d.get("tape_time")) or parse_iso(d.get("time")) or parse_iso(d.get("updated_at"))
    return {"price": price, "mid": None, "bid": None, "ask": None, "ts": ts, "quote_age_ms": None,
            "market_time": d.get("market_time"), "src": "stock-state"}


def parse_levels(raw):
    d = unwrap(raw)
    if isinstance(d, list) and d:
        d = d[0]
    if not isinstance(d, dict):
        return None
    flips = [x for x in (num(v) for v in (d.get("nearby_flips") or [])) if x is not None]
    flip = num(d.get("gamma_flip"))
    if flip is None and flips:
        flip = flips[0]
    if flip is not None and not flips:
        flips = [flip]
    out = {"flip": flip, "flips": flips, "call": num(d.get("call_wall")), "put": num(d.get("put_wall")),
           "magnet": num(d.get("gamma_magnet")), "source": d.get("source"),
           "time": parse_iso(d.get("time")), "date": d.get("date")}
    return out


def parse_ticks(raw):
    d = unwrap(raw)
    if isinstance(d, dict):
        d = d.get("data", [])
    if not isinstance(d, list):
        return None
    out = []
    for r in d:
        if not isinstance(r, dict):
            continue
        t = parse_iso(r.get("tape_time"))
        if t is None:
            continue
        n = lambda k: (num(r.get(k)) if num(r.get(k)) is not None else 0.0)  # noqa: E731
        out.append({"t": t, "ncp": n("net_call_premium"), "npp": n("net_put_premium"),
                    "ncv": n("net_call_volume"), "npv": n("net_put_volume"), "nd": n("net_delta")})
    out.sort(key=lambda x: x["t"])
    return out


OPT_RE = re.compile(r"^([A-Z.]{1,6})(\d{6})([CP])(\d{8})$")


def flow_sign(typ: str, prem, ask, bid):
    """返回 (sign, side)。call 买/put 卖 = 偏多(+1)；put 买/call 卖 = 偏空(-1)；混合/未知 = 0。"""
    if not prem or ask is None or bid is None:
        return 0, "mix"
    lean = (ask - bid) / prem
    if abs(lean) < 0.30:
        return 0, "mix"
    buy = lean > 0
    is_call = (typ == "call")
    return (1 if buy == is_call else -1), ("ask" if buy else "bid")


def parse_flow(raw, today: date):
    d = unwrap(raw)
    if isinstance(d, dict):
        d = d.get("data", [])
    if not isinstance(d, list):
        return None
    out = []
    for r in d:
        if not isinstance(r, dict):
            continue
        t = parse_iso(r.get("created_at"))
        if t is None:
            continue
        typ = str(r.get("type") or "").lower()
        strike = num(r.get("strike"))
        expiry = r.get("expiry")
        chain = r.get("option_chain")
        if chain:
            m = OPT_RE.match(str(chain))
            if m:
                if not typ:
                    typ = "call" if m.group(3) == "C" else "put"
                if strike is None:
                    strike = int(m.group(4)) / 1000.0
                if not expiry:
                    yy, mm, dd = m.group(2)[:2], m.group(2)[2:4], m.group(2)[4:6]
                    expiry = f"20{yy}-{mm}-{dd}"
        dte = None
        if expiry:
            try:
                dte = (date.fromisoformat(str(expiry)[:10]) - today).days
            except ValueError:
                dte = None
        prem = num(r.get("total_premium"))
        ask = num(r.get("total_ask_side_prem"))
        bid = num(r.get("total_bid_side_prem"))
        sign, side = flow_sign(typ, prem, ask, bid)
        key = f"{chain or (typ, strike, expiry)}|{iso(t)}|{int(prem or 0)}|{r.get('alert_rule')}"
        out.append({"key": key, "t": iso(t), "tdt": t, "sign": sign, "side": side, "prem": prem or 0.0,
                    "type": typ, "strike": strike, "dte": dte, "rule": r.get("alert_rule"),
                    "iv": num(r.get("iv")), "delta": num(r.get("delta")), "gamma": num(r.get("gamma")),
                    "vega": num(r.get("vega")), "chain": chain, "sweep": bool(r.get("has_sweep")),
                    "size": num(r.get("total_size"))})
    out.sort(key=lambda x: x["tdt"])
    return out


def parse_greek(raw):
    d = unwrap(raw)
    if isinstance(d, dict):
        d = [d]
    if not isinstance(d, list) or not d:
        return None
    rows = [r for r in d if isinstance(r, dict)]
    if not rows:
        return None
    rows.sort(key=lambda r: str(r.get("date") or ""))
    r = rows[-1]
    cg, pg = num(r.get("call_gamma")), num(r.get("put_gamma"))
    if cg is None or pg is None:
        return None
    gross = abs(cg) + abs(pg)
    return {"date": str(r.get("date") or "")[:10], "net": cg + pg, "ratio": ((cg + pg) / gross) if gross else 0.0}


# ----------------------------------------------------------------------------
# 分析函数
# ----------------------------------------------------------------------------
def compute_zone(lv, cfg: Cfg, buf=None):
    """Flip 区：最近一个 Flip 为中心，把半径内的其他穿越点并入，上下各加缓冲。"""
    if not lv or lv.get("flip") is None:
        return None
    flip = lv["flip"]
    flips = lv.get("flips") or [flip]
    cluster = [f for f in flips if abs(f - flip) <= cfg.zone_radius] or [flip]
    lo, hi = min(cluster), max(cluster)
    b = cfg.flip_buffer if buf is None else buf
    return {"center": flip, "lo": lo, "hi": hi, "low": lo - b, "high": hi + b, "n": len(cluster), "buf": b}


def tide_stats(ticks, now_u: datetime, window_min: float, sigma_prev, cfg: Cfg):
    """x = 每分钟(call 净权利金 − put 净权利金)，正=看多倾向。"""
    xs = [(t["t"], t["ncp"] - t["npp"]) for t in ticks]
    cut = now_u - timedelta(minutes=window_min)
    recent = [x for (tt, x) in xs if tt > cut]
    past = [x for (tt, x) in xs if tt <= cut]
    S = sum(recent)
    sigma = None
    if len(past) >= cfg.tide_min_ticks:
        try:
            sigma = statistics.pstdev(past)
        except statistics.StatisticsError:
            sigma = None
    if (sigma is None or sigma <= 0) and sigma_prev:
        sigma = sigma_prev
    z = None
    if sigma and sigma > 0 and recent:
        z = S / (sigma * math.sqrt(len(recent)))
    return {"S": S, "z": z, "n": len(recent), "sigma": sigma,
            "ncp_day": sum(t["ncp"] for t in ticks), "npp_day": sum(t["npp"] for t in ticks),
            "last": ticks[-1]["t"] if ticks else None, "n_all": len(ticks)}


def realized_sigma_1m_pct(px_hist):
    """用 15 秒级价格样本折算成分钟收盘，估计近 90 分钟的每分钟波动（百分比）。"""
    closes = {}
    for ts, p in px_hist:
        closes[int(ts // 60)] = p
    keys = sorted(closes)
    rets = [(closes[b] / closes[a] - 1.0) * 100.0 for a, b in zip(keys, keys[1:]) if b - a == 1]
    if len(rets) < 20:
        return None
    try:
        return statistics.pstdev(rets)
    except statistics.StatisticsError:
        return None


def sigma_from_ticks(ticks):
    xs = [t["ncp"] - t["npp"] for t in ticks]
    if len(xs) < 100:
        return None
    try:
        v = statistics.pstdev(xs)
    except statistics.StatisticsError:
        return None
    return v if v > 0 else None


# ----------------------------------------------------------------------------
# 状态
# ----------------------------------------------------------------------------
def new_state(date_str: str) -> dict:
    return {
        "v": STATE_VERSION, "date": date_str,
        "panel": {"message_id": None, "last_edit": None},
        "session": {"open": None, "high": None, "low": None, "first_t": None, "was_regular": False},
        "pivot": None, "px_hist": [], "impulse_state": None, "breaks": [], "flip_cross_ts": [],
        "zone": {"side": None, "pending": None, "last": None},
        "walls": {"call_ref": None, "put_ref": None, "pending": {"call": None, "put": None}},
        "broken": {"call": None, "put": None},
        "hist": {"primary": [], "live": []},
        "flags": {"migration": None, "wall_shift": None},
        "events": [], "day_events": [],
        "flow": {"seen": [], "items": [], "tide_state": None, "prints_state": None,
                 "sigma_prev": None, "sigma_prev_done": False},
        "run": None, "last_push": {}, "outbox": [],
        "outage": {"since": None, "notified": False},
        "notified": {}, "digest_close": False, "greek": None,
        "counters": {"cycles": 0, "pushed": 0, "silent": 0, "sent": 0, "loud_capped": 0},
        "prev_price": None,
    }


def load_state(path: str) -> dict:
    try:
        with open(path, "r", encoding="utf-8") as fh:
            st = json.load(fh)
        if isinstance(st, dict) and st.get("v") == STATE_VERSION:
            return st
    except (OSError, ValueError):
        pass
    return new_state("")


def save_state(path: str, st: dict) -> None:
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        json.dump(st, fh, ensure_ascii=False, separators=(",", ":"))
    os.replace(tmp, path)


# ----------------------------------------------------------------------------
# 引擎：逐周期更新信号 → 事件 → 共振 → 推送队列
# ----------------------------------------------------------------------------
class Engine:
    def __init__(self, cfg: Cfg, state: dict | None = None):
        self.cfg = cfg
        self.s = state if state else new_state("")
        self.new_events: list = []
        self.view: dict = {}

    # ---------- 通用 ----------
    @staticmethod
    def age_min(iso_s, now) -> float:
        t = parse_iso(iso_s)
        return (now - t).total_seconds() / 60.0 if t else 1e9

    def cooldown_ok(self, now, key, minutes) -> bool:
        last = self.s["last_push"].get(key)
        return (not last) or self.age_min(last, now) >= minutes

    def once_per_day(self, key) -> bool:
        today = self.s["date"]
        if self.s["notified"].get(key) == today:
            return False
        self.s["notified"][key] = today
        return True

    def add_event(self, now, kind, d, text, price, **extra):
        e = {"t": iso(now), "kind": kind, "dir": d, "text": text,
             "px": round(price, 2) if price is not None else None}
        e.update(extra)
        s = self.s
        s["events"].append(e)
        s["day_events"].append(e)
        keep = self.cfg.struct_fresh_min + 10
        s["events"] = [x for x in s["events"] if self.age_min(x["t"], now) <= keep][-400:]
        s["day_events"] = s["day_events"][-300:]
        self.new_events.append(e)
        return e

    def queue_push(self, now, kind, text, silent=False):
        s = self.s
        if kind in ("conf", "single", "mega", "conf_run") and not silent:
            key, cap, what = (("loud_run", self.cfg.run_cap, "延续/升级提醒") if kind == "conf_run"
                              else ("loud_capped", self.cfg.daily_cap, "信号"))
            if s["counters"].get(key, 0) >= cap:                         # 防刷屏：超过当日上限自动转静音
                silent = True
                text += f"\n（今日已推送 {cap} 条带提示音的{what}，之后改为静音提示）"
            else:
                s["counters"][key] = s["counters"].get(key, 0) + 1
        s["outbox"].append({"t": iso(now), "kind": kind, "text": text, "silent": bool(silent), "attempts": 0})
        s["counters"]["silent" if silent else "pushed"] += 1

    def reset_day(self, today: str):
        old = self.s
        self.s = new_state(today)
        self.s["notified"] = old.get("notified", {})
        self.s["outbox"] = old.get("outbox", [])
        self.s["greek"] = None

    # ---------- 价格基础信息 ----------
    def update_session(self, now, P):
        ss = self.s["session"]
        if ss["open"] is None:
            ss["open"], ss["first_t"] = P, iso(now)
        ss["high"] = P if ss["high"] is None else max(ss["high"], P)
        ss["low"] = P if ss["low"] is None else min(ss["low"], P)

    def update_px_hist(self, now, P):
        ts = now.timestamp()
        ph = self.s["px_hist"]
        ph.append([ts, P])
        self.s["px_hist"] = [x for x in ph if x[0] >= ts - 95 * 60][-500:]
        self.view["sigma1m"] = realized_sigma_1m_pct(self.s["px_hist"])

    def flip_buffer(self, P) -> float:
        sg = self.view.get("sigma1m")
        if not sg:
            return self.cfg.flip_buffer
        return max(self.cfg.flip_buffer, self.cfg.buffer_vol_mult * (sg / 100.0 * P) * math.sqrt(5))

    # ---------- 结构 1：Flip 区 ----------
    def update_zone(self, now, P, prev_P, zone):
        cfg, zs = self.cfg, self.s["zone"]
        if zone is None:
            zs["pending"] = None
            return
        prev_zone = zs.get("last")
        zs["last"] = zone
        side_now = "above" if P > zone["high"] else ("below" if P < zone["low"] else "inside")
        if zs["side"] is None:
            zs["side"] = side_now if side_now != "inside" else ("above" if P >= zone["center"] else "below")
            return
        if side_now == "inside" or side_now == zs["side"]:
            zs["pending"] = None
            return
        pend = zs.get("pending")
        if not pend or pend["side"] != side_now:
            dP = abs(P - prev_P) if prev_P is not None else 0.0
            dZ = abs(zone["center"] - prev_zone["center"]) if prev_zone else 0.0
            zs["pending"] = {"side": side_now, "since": iso(now), "driver": "price" if dP >= dZ else "flip"}
            return
        held = (now - parse_iso(pend["since"])).total_seconds()
        if held >= cfg.flip_confirm_s:
            zs["side"], zs["pending"] = side_now, None
            d = "up" if side_now == "above" else "down"
            rng = f"{zone['lo']:.2f}–{zone['hi']:.2f}" if zone["hi"] - zone["lo"] >= 0.01 else f"{zone['center']:.2f}"
            drv = "价格走出" if pend.get("driver") == "price" else "Flip 区自身移动导致"
            ts = now.timestamp()
            fc = [t for t in self.s["flip_cross_ts"] if t >= ts - cfg.chop_window_min * 60] + [ts]
            self.s["flip_cross_ts"] = fc
            chop = len(fc) >= cfg.chop_crosses
            text = (f"Flip区{'向上' if d == 'up' else '向下'}穿越已确认（Flip {rng}，现价 {P:.2f}，"
                    f"在区外持续 {held:.0f}秒；{drv}）")
            if chop:
                text += f"\n  ⚠ {cfg.chop_window_min:.0f}分钟内第{len(fc)}次穿越，Flip 附近来回震荡，可靠性较低（不计入结构确认）"
            self.add_event(now, "flip_cross", d, text, P, chop=chop)
            if not chop:
                self.register_break(now, d, zone["high"] if d == "up" else zone["low"], "Flip区")

    # ---------- 结构 2：Call/Put Wall 突破 ----------
    def update_walls(self, now, P, prev_P, lv):
        cfg, ws = self.cfg, self.s["walls"]
        if lv is None:
            return
        buf = cfg.wall_buffer
        for kind, d in (("call", "up"), ("put", "down")):
            ref = ws.get(f"{kind}_ref")
            pend = ws["pending"].get(kind)
            if ref is not None and prev_P is not None and not pend:
                crossed = (P > ref + buf and prev_P <= ref + buf) if kind == "call" else \
                          (P < ref - buf and prev_P >= ref - buf)
                if crossed:
                    ws["pending"][kind] = pend = {"level": ref, "since": iso(now)}
            if pend:
                lvl = pend["level"]
                beyond = (P > lvl) if kind == "call" else (P < lvl)
                if not beyond:
                    ws["pending"][kind] = None
                else:
                    held = (now - parse_iso(pend["since"])).total_seconds()
                    if held >= cfg.wall_confirm_s:
                        ws["pending"][kind] = None
                        self.s["broken"][kind] = {"level": lvl, "t": iso(now)}
                        name = "Call Wall" if kind == "call" else "Put Wall"
                        text = (f"{name} {lvl:.2f} {'向上突破' if d == 'up' else '向下跌破'}已确认"
                                f"（现价 {P:.2f}，已越过 {abs(P - lvl):.2f}，持续 {held:.0f}秒）")
                        self.add_event(now, "wall_break", d, text, P, level=lvl)
                        self.register_break(now, d, lvl, name)
            br = self.s["broken"].get(kind)
            if br:
                reclaimed = (P < br["level"] - buf) if kind == "call" else (P > br["level"] + buf)
                if reclaimed or self.age_min(br["t"], now) > cfg.struct_fresh_min:
                    self.s["broken"][kind] = None
            if lv.get(kind) is not None:
                ws[f"{kind}_ref"] = lv[kind]

    # ---------- 动量 A：破位后延伸（没有反转回突破位就一直追，不设时间上限） ----------
    def register_break(self, now, d, level, label):
        self.s["breaks"].append({"d": d, "level": level, "label": label, "t": iso(now), "next": self.cfg.cont_pct})
        self.s["breaks"] = self.s["breaks"][-6:]

    def update_breaks(self, now, P):
        cfg, keep = self.cfg, []
        for b in self.s["breaks"]:
            lvl, d = b["level"], b["d"]
            if (P < lvl) if d == "up" else (P > lvl):
                continue                      # 回到突破位另一侧：这次突破失败，停止追踪
            prog = abs(pct_change(P, lvl))
            if prog >= b["next"]:
                mins = self.age_min(b["t"], now)
                text = (f"破位延续：{b['label']}{'上破' if d == 'up' else '下破'}后继续{'上行' if d == 'up' else '下行'} "
                        f"{prog:.2f}%（突破位 {lvl:.2f}→现价 {P:.2f}，距确认 {mins:.0f}分钟）")
                self.add_event(now, "continuation", d, text, P, prog=round(prog, 3))
                b["next"] = (prog // cfg.cont_step + 1) * cfg.cont_step
            keep.append(b)
        self.s["breaks"] = keep

    # ---------- 动量 B：快速异动（N 分钟内自低点/高点的同向幅度） ----------
    def update_impulse(self, now, P):
        cfg, s = self.cfg, self.s
        ts = now.timestamp()
        win = [p for (t, p) in s["px_hist"] if t >= ts - cfg.impulse_min * 60]
        self.view["impulse"] = None
        if len(win) < 4:
            return
        thr = cfg.impulse_pct
        sg = self.view.get("sigma1m")
        if sg:
            thr = max(thr, cfg.impulse_sigma * sg * math.sqrt(cfg.impulse_min))
        lo, hi = min(win), max(win)
        up, dn = pct_change(P, lo), pct_change(P, hi)       # up >= 0, dn <= 0
        self.view["impulse"] = {"up": up, "dn": dn, "thr": thr}
        d = "up" if (up >= thr and up >= -dn) else ("down" if dn <= -thr else None)
        st = s["impulse_state"]
        if d:
            if st != d:
                mv, ref = (up, lo) if d == "up" else (dn, hi)
                self.add_event(now, "impulse", d,
                               f"快速{'拉升' if d == 'up' else '下杀'} {mv:+.2f}%（{cfg.impulse_min:.0f}分钟内 {ref:.2f}→{P:.2f}，阈值 ±{thr:.2f}%）", P,
                               move=round(mv, 3))
                s["impulse_state"] = d
        elif (st == "up" and up < thr * 0.5) or (st == "down" and dn > -thr * 0.5):
            s["impulse_state"] = None

    # ---------- 里程碑：参考点每走出 ±MOMENTUM_PCT% 记一次（仅面板 / 可选的单独推送） ----------
    def update_momentum(self, now, P):
        cfg, s = self.cfg, self.s
        pv = s["pivot"]
        if pv is None:
            s["pivot"] = {"price": P, "t": iso(now)}
            return
        move = pct_change(P, pv["price"])
        if abs(move) >= cfg.momentum_pct:
            d = "up" if move > 0 else "down"
            mins = self.age_min(pv["t"], now)
            text = (f"价格里程碑{'上行' if d == 'up' else '下行'} {move:+.2f}%（{pv['price']:.2f}→{P:.2f}，"
                    f"用时 {mins:.0f}分钟）")
            self.add_event(now, "milestone", d, text, P, move=round(move, 3))
            s["pivot"] = {"price": P, "t": iso(now)}

    # ---------- 盘中口径：Flip 迁移 / 墙位同向移动（边沿触发） ----------
    def update_hist(self, now, snap):
        for name, key in (("primary", "primary"), ("live", "live")):
            lv = snap.get(key)
            if lv is None or not snap["fresh"].get(key):
                continue
            hist = self.s["hist"][name]
            ts = now.timestamp()
            if hist and ts - hist[-1]["ts"] < 55:
                continue
            hist.append({"ts": ts, "px": self.view.get("P"), "flip": lv.get("flip"),
                         "call": lv.get("call"), "put": lv.get("put"), "magnet": lv.get("magnet")})
            cutoff = ts - (self.cfg.struct_fresh_min + 30) * 60
            self.s["hist"][name] = [h for h in hist if h["ts"] >= cutoff][-400:]

    def update_structure_edges(self, now, P):
        cfg, s = self.cfg, self.s
        hist = s["hist"]["live"]
        new = {"migration": None, "wall_shift": None}
        if len(hist) >= 2:
            cur = hist[-1]
            target = now.timestamp() - cfg.migrate_window_min * 60
            ref = None
            for h in hist:
                if h["ts"] <= target:
                    ref = h
            if ref is None and hist[0]["ts"] <= now.timestamp() - 0.6 * cfg.migrate_window_min * 60:
                ref = hist[0]
            if ref is not None and ref is not cur and ref.get("px") is not None:
                dP = P - ref["px"]
                if cur.get("flip") is not None and ref.get("flip") is not None:
                    df = cur["flip"] - ref["flip"]
                    if df >= cfg.flip_migrate and dP > 0:
                        new["migration"] = {"dir": "up", "df": round(df, 2)}
                    elif df <= -cfg.flip_migrate and dP < 0:
                        new["migration"] = {"dir": "down", "df": round(df, 2)}
                dc = (cur["call"] - ref["call"]) if cur.get("call") is not None and ref.get("call") is not None else 0.0
                dw = (cur["put"] - ref["put"]) if cur.get("put") is not None and ref.get("put") is not None else 0.0
                if (dc >= cfg.wall_shift or dw >= cfg.wall_shift) and dP > 0 and dc >= 0 and dw >= 0:
                    new["wall_shift"] = {"dir": "up", "dc": round(dc, 2), "dw": round(dw, 2)}
                elif (dc <= -cfg.wall_shift or dw <= -cfg.wall_shift) and dP < 0 and dc <= 0 and dw <= 0:
                    new["wall_shift"] = {"dir": "down", "dc": round(dc, 2), "dw": round(dw, 2)}
        old = s["flags"]
        if new["migration"] and (not old.get("migration") or old["migration"]["dir"] != new["migration"]["dir"]):
            m = new["migration"]
            self.add_event(now, "migration", m["dir"],
                           f"盘中Flip{'上移' if m['dir'] == 'up' else '下移'} {m['df']:+.2f}（{cfg.migrate_window_min:.0f}分钟，与价格同向）", P)
        if new["wall_shift"] and (not old.get("wall_shift") or old["wall_shift"]["dir"] != new["wall_shift"]["dir"]):
            w = new["wall_shift"]
            self.add_event(now, "wall_shift", w["dir"],
                           f"墙位同向{'上移' if w['dir'] == 'up' else '下移'}（Call {w['dc']:+.2f} / Put {w['dw']:+.2f}）", P)
        s["flags"] = new

    # ---------- 资金流 ----------
    def update_flow(self, now, P, snap):
        cfg, f = self.cfg, self.s["flow"]
        now_u = now.astimezone(UTC)
        for it in snap.get("flow_new") or []:
            if it["key"] in f["seen"]:
                continue
            f["seen"].append(it["key"])
            f["items"].append({k: it[k] for k in ("t", "sign", "side", "prem", "type", "strike", "dte", "rule", "iv", "delta")})
            fresh = (now_u - it["tdt"]).total_seconds() <= 600
            if fresh and it["prem"] >= cfg.mega_min:
                d = {1: "up", -1: "down"}.get(it["sign"])
                self.add_event(now, "mega", d, self.describe_print(it, now), P, prem=it["prem"])
        f["seen"] = f["seen"][-400:]
        f["items"] = [x for x in f["items"] if self.age_min(x["t"], now) <= 90][-300:]

        # 大单窗口合计
        win = [x for x in f["items"] if self.age_min(x["t"], now) <= cfg.print_window_min and x["prem"] >= cfg.print_min]
        up = sum(x["prem"] for x in win if x["sign"] > 0)
        dn = sum(x["prem"] for x in win if x["sign"] < 0)
        n_up = sum(1 for x in win if x["sign"] > 0)
        n_dn = sum(1 for x in win if x["sign"] < 0)
        cur = None
        if up >= cfg.print_burst and n_up >= cfg.print_min_count and up >= cfg.print_dominance * dn:
            cur = "up"
        elif dn >= cfg.print_burst and n_dn >= cfg.print_min_count and dn >= cfg.print_dominance * up:
            cur = "down"
        if cur:
            if cur != f["prints_state"]:
                tot, cnt = (up, n_up) if cur == "up" else (dn, n_dn)
                self.add_event(now, "prints", cur,
                               f"大单偏{'多' if cur == 'up' else '空'}：近{cfg.print_window_min:.0f}分钟同向合计 {money(tot)}（{cnt}笔）",
                               P, prem=tot)
            f["prints_state"] = cur
        elif max(up, dn) < 0.5 * cfg.print_burst:
            f["prints_state"] = None
        self.view["prints"] = {"up": up, "dn": dn, "n_up": n_up, "n_dn": n_dn}

        # 每分钟净权利金（tide）
        ticks = snap.get("ticks")
        self.view["tide"] = None
        if ticks:
            tide = tide_stats(ticks, now_u, cfg.tide_window_min, f.get("sigma_prev"), cfg)
            self.view["tide"] = tide
            z = tide["z"]
            if z is not None:
                cur = None
                if z >= cfg.tide_z and tide["S"] >= cfg.tide_abs_min:
                    cur = "up"
                elif z <= -cfg.tide_z and tide["S"] <= -cfg.tide_abs_min:
                    cur = "down"
                if cur:
                    if cur != f["tide_state"]:
                        self.add_event(now, "tide", cur,
                                       f"资金流偏{'多' if cur == 'up' else '空'}：近{cfg.tide_window_min:.0f}分钟净倾向 "
                                       f"{money(tide['S'], True)}（z={z:+.1f}）", P, S=round(tide["S"]))
                    f["tide_state"] = cur
                elif abs(z) < cfg.tide_z * 0.6:
                    f["tide_state"] = None

    def describe_print(self, it, now) -> str:
        dte = it.get("dte")
        dte_s = "0DTE" if dte == 0 else (f"{dte}DTE" if dte is not None else "")
        side = {"ask": "主动买入(ask侧)", "bid": "主动卖出(bid侧)", "mix": "买卖混合"}.get(it.get("side"), "")
        bias = {1: "→偏多", -1: "→偏空", 0: "→方向不明"}[it.get("sign", 0)]
        greeks = []
        if it.get("delta") is not None:
            greeks.append(f"Δ{it['delta']:+.2f}")
        if it.get("iv") is not None:
            iv = it["iv"] * 100 if it["iv"] < 3 else it["iv"]
            greeks.append(f"IV {iv:.1f}%")
        g = "｜" + " ".join(greeks) if greeks else ""
        strike = f"{it['strike']:g}" if it.get("strike") is not None else "?"
        return (f"巨额单 {money(it['prem'])}：{(it.get('type') or '').upper()} {strike} {dte_s} {side} {bias}"
                f"（{it.get('rule') or ''}）{g}").replace("  ", " ")

    # ---------- 结构证据 / 三大类状态 ----------
    def struct_evidence(self, now) -> dict:
        cfg, s = self.cfg, self.s
        out = {"up": [], "down": []}
        zs = s["zone"]
        for e in reversed(s["events"]):
            if e["kind"] == "flip_cross" and self.age_min(e["t"], now) <= cfg.struct_fresh_min:
                d = e["dir"]
                ok_side = (d == "up" and zs["side"] == "above") or (d == "down" and zs["side"] == "below")
                if ok_side and e.get("chop"):          # 震荡中的穿越：只有价格已明显离开 Flip 才算
                    zone, P = zs.get("last"), self.view.get("P")
                    far = bool(zone and P and abs(P - zone["center"]) / P * 100 >= cfg.chop_clear_pct
                               and ((P > zone["center"]) == (d == "up")))
                    ok_side = far
                if ok_side:
                    out[d].append(("flip_cross", f"Flip区{'向上' if d == 'up' else '向下'}穿越（{hm(parse_iso(e['t']))}确认）"))
                break
        for kind, d in (("call", "up"), ("put", "down")):
            br = s["broken"].get(kind)
            if br:
                out[d].append(("wall_break", f"{'Call' if kind == 'call' else 'Put'} Wall {br['level']:.2f} "
                                             f"{'上破' if d == 'up' else '下破'}（{hm(parse_iso(br['t']))}确认，尚未收复）"))
        m = s["flags"].get("migration")
        if m:
            out[m["dir"]].append(("migration", f"盘中Flip{'上移' if m['dir'] == 'up' else '下移'} {m['df']:+.2f}"))
        w = s["flags"].get("wall_shift")
        if w:
            out[w["dir"]].append(("wall_shift", f"墙位同向{'上移' if w['dir'] == 'up' else '下移'}"))
        return out

    def categories(self, now, d):
        cfg, evs = self.cfg, self.s["events"]
        st = self.struct_evidence(now)[d]
        tags = {t for t, _ in st}
        # 必须有"真实的穿越/突破"才算结构确认；Flip 迁移、墙位移动只是辅助证据（防止随价格漂移造成误判）
        struct_ok = ("flip_cross" in tags) or ("wall_break" in tags)
        mom = [e for e in evs if e["dir"] == d and e["kind"] in ("impulse", "continuation")
               and self.age_min(e["t"], now) <= cfg.conf_window_min]
        flow = [e for e in evs if e["dir"] == d and e["kind"] in ("tide", "prints", "mega")
                and self.age_min(e["t"], now) <= cfg.conf_window_min]
        return struct_ok, st, mom, flow

    # ---------- 共振判定与"同一波行情"去重 ----------
    def eval_confluence(self, now, P) -> list:
        cfg, s = self.cfg, self.s
        pushed = []
        for d in ("up", "down"):
            if not any(e["dir"] == d for e in self.new_events):
                continue
            struct_ok, st, mom, flow = self.categories(now, d)
            count = int(struct_ok) + int(bool(mom)) + int(bool(flow))
            if count < 2:
                continue
            run, kind = s["run"], None
            if run and run["dir"] == d:
                since = self.age_min(run["last_push"], now)
                prog = pct_change(P, run["last_price"]) * (1 if d == "up" else -1)
                if count > run["tier"] and since >= 1:
                    kind = "upgrade"
                elif since >= cfg.repush_min and prog >= cfg.repush_pct:
                    kind = "continue"
            elif self.cooldown_ok(now, f"conf_{d}", cfg.conf_cooldown_min):
                kind = "new"
            if not kind:
                continue
            text = self.build_confluence(now, P, d, struct_ok, st, mom, flow, count, kind, run)
            self.queue_push(now, "conf" if kind == "new" else "conf_run", text, silent=False)
            s["last_push"][f"conf_{d}"] = iso(now)
            anchored = any(b["d"] == d for b in s["breaks"])      # 有尚未被收复的真实突破作锚点
            if kind == "new":
                s["run"] = {"dir": d, "start": iso(now), "start_price": P, "last_push": iso(now), "last_price": P,
                            "tier": count, "pushes": 1, "extreme": P, "anchored": anchored}
            else:
                run.update(last_push=iso(now), last_price=P, tier=max(run["tier"], count), pushes=run["pushes"] + 1)
            pushed.append(d)
        return pushed

    def check_run(self, now, P):
        cfg, s = self.cfg, self.s
        run = s["run"]
        if not run:
            return
        d = run["dir"]
        run["extreme"] = max(run["extreme"], P) if d == "up" else min(run["extreme"], P)
        retrace = (run["extreme"] - P) / run["extreme"] * 100 if d == "up" else (P - run["extreme"]) / run["extreme"] * 100
        reason = None
        if run.get("anchored") and not any(b["d"] == d for b in s["breaks"]):
            reason = "结构锚点失效（价格已收复 Flip 区 / 突破位）"
        elif retrace >= cfg.run_retrace_pct:
            reason = f"自{'高' if d == 'up' else '低'}点 {run['extreme']:.2f} 回撤 {retrace:.2f}%"
        if reason:
            if run["pushes"] >= 1:
                move = pct_change(P, run["start_price"])
                text = (f"↩ {cfg.symbol} {dir_label(d)}信号失效 · {hm(now)} ET\n原因：{reason}\n"
                        f"自 {hm(parse_iso(run['start']))} 首次提醒起，价格 {run['start_price']:.2f}→{P:.2f}（{move:+.2f}%）\n{DISCLAIMER}")
                self.queue_push(now, "invalid", text, silent=True)
            s["run"] = None

    # ---------- 单一事件推送（可配置） + 巨额单 ----------
    def single_pushes(self, now, P, conf_dirs):
        cfg = self.cfg
        for e in self.new_events:
            d, kind = e["dir"], e["kind"]
            if kind == "mega":
                if d in conf_dirs:
                    continue
                if self.cooldown_ok(now, f"mega_{d}", cfg.mega_cooldown_min):
                    self.s["last_push"][f"mega_{d}"] = iso(now)
                    self.queue_push(now, "mega", self.build_simple(now, P, "🐋", f"{cfg.symbol} 巨额单", e["text"]), silent=False)
                continue
            if d in conf_dirs:
                continue
            if kind == "flip_cross" and e.get("chop"):
                continue
            want = False
            if cfg.push_single == "all" and kind in ("flip_cross", "wall_break", "impulse", "continuation", "milestone",
                                                     "tide", "prints", "migration", "wall_shift"):
                want = True
            elif cfg.push_single == "structure" and kind in ("flip_cross", "wall_break"):
                want = True
            if want and self.cooldown_ok(now, f"single_{kind}_{d}", cfg.single_cooldown_min):
                self.s["last_push"][f"single_{kind}_{d}"] = iso(now)
                note = "目前仅为单一信号；动量 / 资金流同向时会另发“共振”提醒"
                self.queue_push(now, "single", self.build_simple(now, P, "⚡", f"{cfg.symbol} {'结构' if kind in ('flip_cross', 'wall_break') else '信号'}事件", e["text"], note), silent=False)

    # ---------- 文本构造 ----------
    def levels_lines(self, P) -> str:
        v = self.view
        prim = v.get("prim") or {}
        zone = self.s["zone"].get("last")
        a = [f"现价 {P:.2f}"]
        if zone:
            rng = f"（区 {zone['lo']:.2f}–{zone['hi']:.2f}）" if zone["hi"] - zone["lo"] >= 0.01 else ""
            a.append(f"Flip {zone['center']:.2f}{rng}")
        b = []
        if prim.get("call") is not None:
            b.append(f"Call Wall {prim['call']:.2f}（{prim['call'] - P:+.2f}）")
        if prim.get("put") is not None:
            b.append(f"Put Wall {prim['put']:.2f}（{prim['put'] - P:+.2f}）")
        if prim.get("magnet") is not None:
            b.append(f"磁吸 {prim['magnet']:.2f}（{prim['magnet'] - P:+.2f}）")
        src = SRC_LABEL.get(self.cfg.primary_src, self.cfg.primary_src)
        return "｜".join(a) + ("\n" + "｜".join(b) if b else "") + f"\n点位口径：{src}"

    def flow_status_text(self) -> str:
        t = self.view.get("tide")
        if not t or t.get("z") is None:
            return "（净权利金基线积累中 / 暂无数据）"
        return f"近{self.cfg.tide_window_min:.0f}分钟净倾向 {money(t['S'], True)}（z={t['z']:+.1f}，未达±{self.cfg.tide_z:g}）"

    def mom_status_text(self, P) -> str:
        imp = self.view.get("impulse")
        if not imp:
            return "（价格样本积累中）"
        return (f"近{self.cfg.impulse_min:.0f}分钟自低点 {imp['up']:+.2f}% / 自高点 {imp['dn']:+.2f}%"
                f"（快速异动需达 ±{imp.get('thr', self.cfg.impulse_pct):.2f}%）")

    def struct_status_text(self) -> str:
        side = self.s["zone"].get("side")
        if side is None:
            return "（Flip 数据缺失）"
        return f"价格在Flip区{'上方' if side == 'above' else '下方'}，暂无新的穿越/破位确认"

    def build_confluence(self, now, P, d, struct_ok, st, mom, flow, count, kind, run) -> str:
        cfg = self.cfg
        if kind == "continue":
            head = f"🔁 {cfg.symbol} 共振延续 {dir_label(d)} · {count}/3 · {hm(now)} ET"
        elif kind == "upgrade":
            head = f"🔔⬆ {cfg.symbol} 共振升级 {dir_label(d)} · {count}/3 · {hm(now)} ET"
        else:
            head = f"🔔 {cfg.symbol} 共振 {dir_label(d)} · {count}/3 · {hm(now)} ET"
        L = [head]
        if struct_ok:
            strong = {"migration", "wall_shift"} <= {t for t, _ in st}
            L.append("结构 ✓ " + "；".join(t for _, t in st) + ("（三项齐备：穿越/突破 + Flip迁移 + 墙位移动）" if strong else ""))
        else:
            L.append("结构 ✗ " + ("；".join(t for _, t in st) + "（证据不足）" if st else self.struct_status_text()))
        L.append("动量 ✓ " + mom[-1]["text"] if mom else "动量 ✗ " + self.mom_status_text(P))
        L.append("资金流 ✓ " + "；".join(e["text"] for e in flow[-2:]) if flow else "资金流 ✗ " + self.flow_status_text())
        if kind == "continue" and run:
            mv = pct_change(P, run["start_price"])
            L.append(f"自 {hm(parse_iso(run['start']))} 首次提醒起，价格 {run['start_price']:.2f}→{P:.2f}（{mv:+.2f}%）")
        L.append("")
        L.append(self.levels_lines(P))
        L.append(self.data_times_line(now))
        L.append(DISCLAIMER)
        return "\n".join(L)

    def build_simple(self, now, P, icon, title, body, note=None) -> str:
        L = [f"{icon} {title} · {hm(now)} ET", body, "", self.levels_lines(P), self.data_times_line(now)]
        if note:
            L.append(note)
        L.append(DISCLAIMER)
        return "\n".join(L)

    def data_times_line(self, now) -> str:
        v = self.view
        parts = []
        age = v.get("price_age")
        if age is not None:
            parts.append(f"价格{fmt_age(age)}前")
        prim, live = v.get("prim"), v.get("live")
        if prim and prim.get("time"):
            parts.append(f"{SRC_LABEL.get(self.cfg.primary_src, 'A')}快照{hm(prim['time'])}")
        if live and live is not prim and live.get("time"):
            parts.append(f"{SRC_LABEL.get(self.cfg.live_src, 'B')}快照{hm(live['time'])}")
        t = v.get("tide")
        if t and t.get("last"):
            parts.append(f"资金流{hm(t['last'])}")
        return "数据时间(ET)：" + " · ".join(parts) if parts else ""

    def build_close_digest(self, now) -> str:
        cfg, s = self.cfg, self.s
        ss, v = s["session"], self.view
        P = v.get("P") or ss.get("high")
        evs = s["day_events"]
        by = {}
        for e in evs:
            by[e["kind"]] = by.get(e["kind"], 0) + 1
        L = [f"📉 {cfg.symbol} 收盘摘要 · {s['date']}"]
        if ss["open"] is not None and P is not None:
            L.append(f"开盘读数 {ss['open']:.2f} → 现价 {P:.2f}（{pct_change(P, ss['open']):+.2f}%）｜日内高 {ss['high']:.2f} 低 {ss['low']:.2f}")
        if v.get("prim") and P is not None:
            L.append(self.levels_lines(P))
        t = v.get("tide")
        if t:
            L.append(f"全天净权利金：Call净 {money(t['ncp_day'], True)}｜Put净 {money(t['npp_day'], True)}（Put净为正=买put多于卖put）")
        g = s.get("greek")
        if g:
            L.append(f"日度净Gamma（OI口径）：{'偏正' if g['net'] > 0 else '偏负'}（净占比 {g['ratio'] * 100:+.0f}%）")
        names = {"flip_cross": "Flip穿越", "wall_break": "墙位突破", "impulse": "快速异动", "continuation": "破位延续",
                 "milestone": "价格里程碑", "tide": "资金流异动",
                 "prints": "大单偏向", "mega": "巨额单", "migration": "Flip迁移", "wall_shift": "墙位移动"}
        if evs:
            L.append("今日事件：" + "｜".join(f"{names.get(k, k)} {n}" for k, n in by.items()))
            key_ev = [e for e in evs if e["kind"] in ("flip_cross", "wall_break", "mega")][-6:]
            for e in key_ev:
                L.append(f"  {hm(parse_iso(e['t']))} {e['text']}")
        else:
            L.append("今日无信号事件")
        L.append(f"共振/事件提醒推送：{s['counters']['pushed']} 条（含本条之前）")
        L.append(DISCLAIMER)
        return "\n".join(L)

    # ---------- 主入口：一个周期 ----------
    def step(self, now, snap) -> dict:
        cfg = self.cfg
        self.new_events = []
        today = now.astimezone(ET).strftime("%Y-%m-%d")
        if self.s.get("date") != today:
            self.reset_day(today)
        s = self.s
        s["counters"]["cycles"] += 1
        now_u = now.astimezone(UTC)
        force = bool(snap.get("force"))
        q = snap.get("quote")
        P = q["price"] if q else None
        price_age = (now_u - q["ts"]).total_seconds() if (q and q.get("ts")) else None
        mt = (q or {}).get("market_time")
        closed = (not force) and mt is not None and mt != "regular"
        stale = (P is None) or (price_age is not None and price_age > cfg.stale_price_s and not closed and not force)
        self.view = {"P": P, "q": q, "price_age": price_age, "closed": closed, "stale": stale, "force": force,
                     "prim": snap.get("primary"), "live": snap.get("live"), "tide": None, "prints": None,
                     "caps": snap.get("caps", {})}
        expect_live = in_window(now, cfg) and not force

        # --- 数据中断检测 ---
        if expect_live and not closed and stale and "daily_limit" not in (snap.get("notices") or {}):
            out = s["outage"]
            if out["since"] is None:
                out["since"] = iso(now)
            down_s = (now - parse_iso(out["since"])).total_seconds()
            if down_s >= cfg.outage_s and not out["notified"]:
                out["notified"] = True
                reason = snap.get("quote_err") or ("价格时间戳过旧" if P is not None else "无法获取价格")
                self.queue_push(now, "outage", f"⚠ {cfg.symbol} 监控数据中断 · {hm(now)} ET\n价格数据已 {fmt_age(down_s)} 无有效更新（{reason}）。"
                                f"恢复后会再通知；期间不会产生信号。", silent=False)
        elif s["outage"]["since"] is not None and P is not None and not stale:
            if s["outage"]["notified"]:
                self.queue_push(now, "recover", f"✅ {cfg.symbol} 监控数据已恢复 · {hm(now)} ET", silent=True)
            s["outage"] = {"since": None, "notified": False}

        # --- 其它一次性告警（权限/认证） ---
        for msg_key, msg in (snap.get("notices") or {}).items():
            if self.once_per_day(msg_key):
                self.queue_push(now, "notice", f"⚠ {cfg.symbol} 监控提示 · {hm(now)} ET\n{msg}", silent=False)

        # --- 收盘摘要（转换为非常规时段，或到点） ---
        if not force and not s["digest_close"] and s["session"]["open"] is not None:
            at = parse_hhmm(cfg.close_digest_at)
            if (closed and s["session"]["was_regular"]) or (now.astimezone(ET).time() >= at):
                self.queue_push(now, "digest", self.build_close_digest(now), silent=False)
                s["digest_close"] = True

        live_ok = (P is not None) and (not stale) and (not closed)
        if live_ok:
            s["session"]["was_regular"] = True
        if not live_ok and not (force and P is not None):
            return {"evaluated": False}

        # --- 正常评估 ---
        prev_P = s.get("prev_price")
        prim = snap.get("primary")
        self.update_px_hist(now, P)
        zone = compute_zone(prim, cfg, self.flip_buffer(P)) if prim else None
        self.update_session(now, P)
        self.update_hist(now, snap)
        self.update_zone(now, P, prev_P, zone)
        self.update_walls(now, P, prev_P, prim)
        self.update_breaks(now, P)
        self.update_impulse(now, P)
        self.update_momentum(now, P)
        self.update_structure_edges(now, P)
        self.update_flow(now, P, snap)
        self.check_run(now, P)          # 先结算旧信号（失效/回撤），再判断是否有新的共振
        conf_dirs = self.eval_confluence(now, P)
        self.single_pushes(now, P, conf_dirs)
        s["prev_price"] = P
        return {"evaluated": True, "events": list(self.new_events)}


# ----------------------------------------------------------------------------
# 面板
# ----------------------------------------------------------------------------
def render_panel(eng: Engine, now) -> str:
    cfg, s, v = eng.cfg, eng.s, eng.view
    P = v.get("P")
    L = [f"📊 {cfg.symbol} 实时面板 · {hm(now, True)} ET"]
    if v.get("force"):
        L.append("🧪 测试模式：非交易时段，下面是最近一个交易日的数据")
    elif v.get("closed"):
        L.append("💤 当前不在常规交易时段（盘前/盘后/休市），信号暂停")
    elif v.get("stale"):
        L.append("⚠ 价格数据异常或过旧，信号暂停")
    if P is not None:
        ss = s["session"]
        if ss["open"] is not None:
            L.append(f"现价 {P:.2f}｜较开盘读数 {pct_change(P, ss['open']):+.2f}%｜高 {ss['high']:.2f} 低 {ss['low']:.2f}")
        else:
            L.append(f"现价 {P:.2f}")
    else:
        L.append("现价：暂无")
    prim, live = v.get("prim"), v.get("live")
    zone = s["zone"].get("last")
    L.append("")
    L.append(f"【结构·{SRC_LABEL.get(cfg.primary_src, cfg.primary_src)}】")
    if zone and P is not None:
        side = s["zone"].get("side")
        side_t = {"above": "上方", "below": "下方"}.get(side, "区内")
        rng = f"{zone['lo']:.2f}–{zone['hi']:.2f}" if zone["hi"] - zone["lo"] >= 0.01 else f"{zone['center']:.2f}"
        pend = s["zone"].get("pending")
        pend_t = f"｜待确认穿越{'上' if pend['side'] == 'above' else '下'}方" if pend else ""
        L.append(f"Flip {rng}｜现价在{side_t}（距中心 {P - zone['center']:+.2f}）{pend_t}")
    elif prim:
        L.append("Flip：无（净Gamma未穿零）")
    if prim and P is not None:
        parts = []
        if prim.get("call") is not None:
            parts.append(f"Call Wall {prim['call']:.2f}（{prim['call'] - P:+.2f}）")
        if prim.get("put") is not None:
            parts.append(f"Put Wall {prim['put']:.2f}（{prim['put'] - P:+.2f}）")
        if parts:
            L.append("｜".join(parts))
        if prim.get("magnet") is not None:
            L.append(f"磁吸位 {prim['magnet']:.2f}（{prim['magnet'] - P:+.2f}）")
    elif not prim:
        L.append("（点位数据暂不可用）")
    for kind, nm in (("call", "Call Wall"), ("put", "Put Wall")):
        br = s["broken"].get(kind)
        if br:
            L.append(f"已{'上破' if kind == 'call' else '下破'} {nm} {br['level']:.2f}（{hm(parse_iso(br['t']))}确认，未收复）")
    if live and live is not prim and P is not None:
        m = s["flags"].get("migration")
        mt = f"｜Flip迁移 {m['df']:+.2f}" if m else ""
        L.append(f"盘中·{SRC_LABEL.get(cfg.live_src, cfg.live_src)}：Flip {fpx(live.get('flip'))}｜Call {fpx(live.get('call'))}｜Put {fpx(live.get('put'))}{mt}")
    g = s.get("greek")
    if g:
        L.append(f"日度净Gamma(OI)：{'偏正（压制波动倾向）' if g['net'] > 0 else '偏负（放大波动倾向）'}｜净占比 {g['ratio'] * 100:+.0f}%")
    L.append("")
    L.append("【资金流】")
    t = v.get("tide")
    if t:
        if t.get("z") is not None:
            z = t["z"]
            lab = "偏多" if z >= 1 else ("偏空" if z <= -1 else "中性")
            L.append(f"近{cfg.tide_window_min:.0f}分钟净倾向 {money(t['S'], True)}（{lab}，z={z:+.1f}）")
        else:
            L.append(f"近{cfg.tide_window_min:.0f}分钟净倾向 {money(t['S'], True)}（基线积累中）")
        L.append(f"全天：Call净 {money(t['ncp_day'], True)}｜Put净 {money(t['npp_day'], True)}")
    else:
        L.append("净权利金：暂无数据")
    pr = v.get("prints")
    if pr and (pr["up"] or pr["dn"]):
        L.append(f"大单（近{cfg.print_window_min:.0f}分钟，≥{money(cfg.print_min)}）：偏多 {money(pr['up'])}（{pr['n_up']}笔）｜偏空 {money(pr['dn'])}（{pr['n_dn']}笔）")
    recent_items = [x for x in s["flow"]["items"] if x["prem"] >= cfg.print_min][-2:]
    if recent_items:
        L.append("最近大单：")
    for it in recent_items:
        dte = it.get("dte")
        L.append(f"  {hm(parse_iso(it['t']))} {(it.get('type') or '?').upper()} {it.get('strike') or '?'} "
                 f"{'0DTE' if dte == 0 else (str(dte) + 'DTE' if dte is not None else '')} {money(it['prem'])} "
                 f"{ {1: '偏多', -1: '偏空', 0: '方向不明'}[it['sign']] }")
    L.append("")
    L.append("【动量】")
    imp = v.get("impulse")
    if imp:
        L.append(f"近{cfg.impulse_min:.0f}分钟：自低点 {imp['up']:+.2f}%｜自高点 {imp['dn']:+.2f}%（快速异动需 ±{imp.get('thr', cfg.impulse_pct):.2f}%）")
    for b in s["breaks"][-2:]:
        if P is not None:
            prog = abs(pct_change(P, b["level"]))
            L.append(f"追踪：{b['label']}{'上破' if b['d'] == 'up' else '下破'}（{b['level']:.2f}，{hm(parse_iso(b['t']))}）后已延伸 {prog:.2f}%（下一档 {b['next']:.2f}%）")
    pv = s["pivot"]
    if pv and P is not None:
        L.append(f"价格里程碑参考点 {pv['price']:.2f}（{hm(parse_iso(pv['t']))}）｜当前 {pct_change(P, pv['price']):+.2f}%｜±{cfg.momentum_pct:g}%记一次")
    L.append("")
    L.append("【共振】")
    now_ = now
    for d in ("up", "down"):
        so, st, mom, flow = eng.categories(now_, d)
        c = int(so) + int(bool(mom)) + int(bool(flow))
        L.append(f"{dir_label(d)} {c}/3｜结构{'✓' if so else '✗'} 动量{'✓' if mom else '✗'} 资金流{'✓' if flow else '✗'}")
    run = s["run"]
    if run and P is not None:
        mv = pct_change(P, run["start_price"])
        L.append(f"进行中：{dir_label(run['dir'])}（{hm(parse_iso(run['start']))}起，价格 {run['start_price']:.2f}→{P:.2f}，{mv:+.2f}%，已提醒{run['pushes']}次）")
    evs = s["events"][-5:]
    if evs:
        L.append("")
        L.append("【最近信号】")
        for e in reversed(evs):
            L.append(f"{hm(parse_iso(e['t']))} {e['text'][:60]}")
    L.append("")
    dt_line = eng.data_times_line(now)
    if dt_line:
        L.append(dt_line)
    caps = v.get("caps") or {}
    bad = [k for k, val in caps.items() if val]
    if bad:
        L.append("⚠ 不可用接口：" + "、".join(bad))
    L.append(DISCLAIMER)
    return "\n".join(L)


# ----------------------------------------------------------------------------
# 数据抓取调度
# ----------------------------------------------------------------------------
class Fetcher:
    def __init__(self, cfg: Cfg, uw: UW, eng: Engine):
        self.cfg, self.uw, self.eng = cfg, uw, eng
        self.last: dict = {}
        self.cache: dict = {}
        self.disabled: dict = {}
        self.errs: dict = {}
        self.fatal = None
        self.pause_until = None

    def due(self, name, now, every) -> bool:
        t = self.last.get(name)
        return t is None or (now - t).total_seconds() >= every

    def fetch(self, name, path, params, parser, now, retries=2):
        if name in self.disabled:
            return None
        self.last[name] = now
        r = self.uw.get(path, params, retries=retries)
        if r.ok:
            val = parser(r.data)
            if val is not None:
                self.cache[name] = val
                self.errs.pop(name, None)
                return val
            self.errs[name] = "返回内容无法解析"
            return None
        self.errs[name] = r.err or f"HTTP {r.status}"
        if r.status in (401, 402):
            self.fatal = r
        elif r.status == 429 and r.code and "daily_request_limit_hit" in r.code:
            self.pause_until = now + timedelta(minutes=30)     # 当日额度用完：暂停轮询，避免空转
        elif r.status in (403, 404, 422):
            self.disabled[name] = f"{r.status} {r.err}"
        return None

    def snapshot(self, now) -> dict:
        cfg, eng, sym = self.cfg, self.eng, self.cfg.symbol
        snap = {"now": now, "force": cfg.force_run, "fresh": {}, "flow_new": [], "notices": {}}
        if self.pause_until and now < self.pause_until:
            snap.update(quote=None, quote_err="已达 UW 每日请求上限，暂停轮询", primary=self.cache.get("lv_primary"),
                        live=self.cache.get("lv_live") or self.cache.get("lv_primary"), ticks=self.cache.get("ticks"),
                        caps={k: v for k, v in self.disabled.items()})
            snap["notices"]["daily_limit"] = "UW 返回“已达每日请求上限”，监控暂停 30 分钟后自动重试。"
            return snap
        # 1) 价格（每个周期）
        qv = self.fetch("quote", f"/api/stock/{sym}/quote", None, parse_quote, now)
        if qv is None and "quote" in self.disabled:
            qv = self.fetch("state", f"/api/stock/{sym}/stock-state", None, parse_stock_state, now)
        snap["quote"] = qv
        snap["quote_err"] = self.errs.get("quote") or self.errs.get("state")
        # 2) 点位
        if self.due("lv_primary", now, cfg.levels_every) or "lv_primary" not in self.cache:
            lv = self.fetch("lv_primary", f"/api/stock/{sym}/gex-levels", {"source": cfg.primary_src}, parse_levels, now)
            snap["fresh"]["primary"] = lv is not None
        snap["primary"] = self.cache.get("lv_primary")
        if cfg.live_src and cfg.live_src != cfg.primary_src:
            if self.due("lv_live", now, cfg.levels_every) or "lv_live" not in self.cache:
                lv = self.fetch("lv_live", f"/api/stock/{sym}/gex-levels", {"source": cfg.live_src}, parse_levels, now)
                snap["fresh"]["live"] = lv is not None
            snap["live"] = self.cache.get("lv_live") or snap["primary"]
        else:
            snap["live"] = snap["primary"]
            snap["fresh"]["live"] = snap["fresh"].get("primary", False)
        # 3) 净权利金（每分钟 tick）
        if self.due("ticks", now, cfg.ticks_every) or "ticks" not in self.cache:
            self.fetch("ticks", f"/api/stock/{sym}/net-prem-ticks", None, parse_ticks, now)
        snap["ticks"] = self.cache.get("ticks")
        # 4) 大单提醒（只取新增）
        if self.due("flow", now, cfg.flow_every) and "flow" not in self.disabled:
            cur = parse_iso(eng.s["flow"].get("cursor")) if eng.s["flow"].get("cursor") else None
            # 回看 5 分钟重叠（按 key 去重），防止个别提醒"迟到入库"被漏掉
            since = (cur - timedelta(minutes=5)) if cur else (now.astimezone(UTC) - timedelta(days=4 if cfg.force_run else 0, minutes=30))
            items = self.fetch("flow", "/api/option-trades/flow-alerts",
                               {"ticker_symbol": sym, "limit": 100, "min_premium": int(cfg.print_min),
                                "newer_than": int(since.timestamp())},
                               lambda raw: parse_flow(raw, now.astimezone(ET).date()), now)
            if items is not None:
                snap["flow_new"] = items
                if items:
                    newest = max(i["tdt"] for i in items)
                    eng.s["flow"]["cursor"] = iso(newest)
        # 5) 每日一次：日度 Gamma、前一交易日 tick 波动基线
        if (eng.s.get("greek") is None) and "greek" not in self.disabled and self.due("greek", now, 600):
            g = self.fetch("greek", f"/api/stock/{sym}/greek-exposure", {"timeframe": "1W"}, parse_greek, now, retries=1)
            if g:
                eng.s["greek"] = g
        fl = eng.s["flow"]
        if not fl["sigma_prev_done"] and "ticks_prev" not in self.disabled:
            for d in prev_weekdays(now.astimezone(ET).date(), 5):
                r = self.uw.get(f"/api/stock/{sym}/net-prem-ticks", {"date": d.isoformat()}, retries=1)
                if not r.ok:
                    break
                tk = parse_ticks(r.data)
                sg = sigma_from_ticks(tk or [])
                if sg:
                    fl["sigma_prev"] = sg
                    break
            fl["sigma_prev_done"] = True
        # 6) 接口异常汇总
        snap["caps"] = {k: v for k, v in self.disabled.items()}
        if self.fatal is not None:
            snap["notices"]["auth"] = f"UW API 访问失败（HTTP {self.fatal.status}：{self.fatal.err}）。请检查 UW_API_KEY 与订阅状态。"
        for k, v in self.disabled.items():
            snap["notices"][f"cap_{k}"] = f"接口 {k} 不可用（{v}），相关信号已停用；其余功能不受影响。"
        return snap


# ----------------------------------------------------------------------------
# 推送投递
# ----------------------------------------------------------------------------
def deliver(cfg: Cfg, tg: Telegram, eng: Engine, now, snap_force: bool = False) -> None:
    s = eng.s
    remaining, blocked = [], False
    for item in s["outbox"]:
        age_m = eng.age_min(item["t"], now)
        if age_m > 20:                       # 太旧的提醒不再补发（过时信息比没有更糟）
            continue
        if blocked:                          # 本周期 Telegram 已出现临时故障：其余留到下个周期
            remaining.append(item)
            continue
        text = item["text"]
        if age_m > 1.5:
            text = f"⏱ 延迟送达（原触发 {hm(parse_iso(item['t']))} ET）\n" + text
        mid = tg.send(text, silent=item["silent"])
        if mid is not None:
            s["counters"]["sent"] += 1
            continue
        log("Telegram 发送失败：", tg.last_error)
        item["attempts"] = item.get("attempts", 0) + 1
        if (tg.last_error or "").startswith("400"):
            continue                         # 这条消息本身被拒（格式问题）：丢弃，不拖累后面的
        blocked = True                       # 网络/限流/5xx：保留重试
        remaining.append(item)
    s["outbox"] = remaining
    if blocked:
        return

    p = s["panel"]
    due = p["last_edit"] is None or (now - parse_iso(p["last_edit"])).total_seconds() >= cfg.panel_every
    if not due:
        return
    text = render_panel(eng, now)
    if p["message_id"] is None:
        mid = tg.send(text, silent=False)
        if mid is not None:
            p["message_id"], p["last_edit"] = mid, iso(now)
        else:
            log("面板发送失败：", tg.last_error)
    else:
        r = tg.edit(p["message_id"], text)
        if r == "ok":
            p["last_edit"] = iso(now)
        elif r == "gone":
            mid = tg.send(text, silent=True)
            if mid is not None:
                p["message_id"], p["last_edit"] = mid, iso(now)
        else:
            log("面板刷新失败：", tg.last_error)


# ----------------------------------------------------------------------------
# 运行模式
# ----------------------------------------------------------------------------
def run_monitor(cfg: Cfg, uw: UW, tg: Telegram, now_fn=now_et, sleep=time.sleep, state_path: str = STATE_FILE) -> None:
    eng = Engine(cfg, load_state(state_path))
    fetcher = Fetcher(cfg, uw, eng)
    start = now_fn()
    consec_err, cycles = 0, 0
    while True:
        now = now_fn()
        if not cfg.force_run and not in_window(now, cfg):
            log(f"非监控时段（{cfg.win_start}-{cfg.win_end} ET 工作日），本次触发直接结束。")
            break
        try:
            snap = fetcher.snapshot(now)
            res = eng.step(now, snap)
            deliver(cfg, tg, eng, now)
            save_state(state_path, eng.s)
            consec_err = 0
            v = eng.view
            log(f"[{hm(now, True)}] 周期{cycles + 1} "
                f"价格{'OK' if v.get('P') is not None and not v.get('stale') else '异常'}"
                f"{'' if not cfg.debug else ' P=' + fpx(v.get('P'))} "
                f"事件{len(res.get('events', [])) if res.get('evaluated') else '-'} "
                f"待发{len(eng.s['outbox'])} UW调用{uw.calls}/错误{uw.errors}")
        except Exception as e:  # noqa: BLE001
            consec_err += 1
            log(f"周期异常（连续第{consec_err}次）：{type(e).__name__}: {safe(e)}")
            if cfg.debug:
                log(safe(traceback.format_exc()))
            if consec_err == 3 and eng.once_per_day("script_error"):
                tg.send(f"⚠ {cfg.symbol} 监控脚本连续出错：{type(e).__name__}。请把 Actions 日志发给我排查。", silent=False)
            if consec_err >= 8:
                log("连续出错次数过多，退出。")
                break
        cycles += 1
        if cfg.force_run:
            break
        if (now_fn() - start).total_seconds() + cfg.poll >= cfg.loop_s:
            break
        sleep(cfg.poll)
    try:
        save_state(state_path, eng.s)
    except OSError as e:
        log("保存状态失败：", e)


def shape(obj, depth: int = 0) -> str:
    if isinstance(obj, dict):
        items = list(obj.items())
        if depth >= 2:
            return "{" + ",".join(k for k, _ in items[:14]) + ("…" if len(items) > 14 else "") + "}"
        return "{" + ", ".join(f"{k}:{shape(v, depth + 1)}" for k, v in items[:16]) + ("…" if len(items) > 16 else "") + "}"
    if isinstance(obj, list):
        return f"[{len(obj)}×{shape(obj[0], depth + 1) if obj else ''}]"
    if isinstance(obj, bool):
        return "bool"
    if isinstance(obj, (int, float)):
        return "num"
    if isinstance(obj, str):
        return "str"
    return "null" if obj is None else type(obj).__name__


def flow_rate_report(items, cfg: Cfg) -> str:
    """把 flow-alerts 的条数 / 金额分布 / 方向分布整理成几行，用来校准大单阈值。"""
    if not items:
        return f"ℹ️ 大单频率统计｜没有 ≥{money(cfg.print_min)} 的记录（可能是休市期间或套餐不含此数据）"
    by_day = {}
    for x in items:
        by_day.setdefault(x["tdt"].astimezone(ET).date(), []).append(x)
    days = sorted(by_day)
    L = [f"📊 大单频率统计（门槛 ≥{money(cfg.print_min)}｜共 {len(items)} 条｜{days[0]}～{days[-1]}）"]
    if len(items) >= 500:
        L.append("   ⚠ 已触到 500 条上限，实际更多 → 建议把 PRINT_MIN_PREMIUM 提高（如 500000 或 1000000）")
    for d in days[-4:]:
        xs = by_day[d]
        pr = sorted(x["prem"] for x in xs)

        def n_ge(v, pr=pr):
            return sum(1 for p in pr if p >= v)

        bull = sum(x["prem"] for x in xs if x["sign"] > 0)
        bear = sum(x["prem"] for x in xs if x["sign"] < 0)
        mix = sum(x["prem"] for x in xs if x["sign"] == 0)
        L.append(f"   {d.strftime('%a %m-%d')}：{len(xs)}条｜≥1M {n_ge(1e6)}｜≥3M {n_ge(3e6)}｜≥5M {n_ge(5e6)}"
                 f"｜中位 {money(pr[len(pr) // 2])}｜最大 {money(pr[-1])}｜偏多 {money(bull)} 偏空 {money(bear)} 中性 {money(mix)}")
    last = by_day[days[-1]]
    hrs = {}
    for x in last:
        hh = x["tdt"].astimezone(ET).hour
        hrs[hh] = hrs.get(hh, 0) + 1
    L.append(f"   {days[-1].strftime('%m-%d')} 分时段（ET）：" + "｜".join(f"{h}时 {hrs[h]}" for h in sorted(hrs)))
    rules = {}
    for x in items:
        rules[x.get("rule") or "?"] = rules.get(x.get("rule") or "?", 0) + 1
    top = sorted(rules.items(), key=lambda kv: -kv[1])[:4]
    L.append("   规则类型：" + "｜".join(f"{k} {n}" for k, n in top))
    return "\n".join(L)


def run_probe(cfg: Cfg, uw: UW, tg: Telegram, now_fn=now_et) -> None:
    now = now_fn()
    sym = cfg.symbol
    today = now.astimezone(ET).date()
    prev = prev_weekdays(today, 1)[0].isoformat()
    now_u = now.astimezone(UTC)
    tests = [
        ("quote", f"/api/stock/{sym}/quote", None),
        ("stock-state(备用价格)", f"/api/stock/{sym}/stock-state", None),
        ("gex-levels oi", f"/api/stock/{sym}/gex-levels", {"source": "oi"}),
        ("gex-levels vol", f"/api/stock/{sym}/gex-levels", {"source": "vol"}),
        ("net-prem-ticks", f"/api/stock/{sym}/net-prem-ticks", None),
        ("net-prem-ticks 前一日", f"/api/stock/{sym}/net-prem-ticks", {"date": prev}),
        ("flow-alerts", "/api/option-trades/flow-alerts", {"ticker_symbol": sym, "limit": 30}),
        ("greek-exposure", f"/api/stock/{sym}/greek-exposure", {"timeframe": "1W"}),
        ("news headlines", "/api/news/headlines", {"limit": 3}),
        ("potus posts", "/api/potus/posts", None),
    ]
    lines_ok, lines_shape, n_ok = [], [], 0
    for name, path, params in tests:
        r = uw.get(path, params, retries=1)
        log(f"probe {name}: HTTP {r.status} {r.ms}ms {'OK' if r.ok else (r.err or '')[:80]}")
        if not r.ok:
            lines_ok.append(f"❌ {name}｜HTTP {r.status}｜{(r.err or '')[:140]}")
            continue
        n_ok += 1
        info = ""
        try:
            if name == "quote":
                q = parse_quote(r.data)
                if q:
                    age = (now_u - q["ts"]).total_seconds() if q["ts"] else None
                    qa = q["quote_age_ms"]
                    info = (f"price {q['price']}｜成交时间 {hmd(q['ts'])} ET（距现在 {fmt_age(age)}）"
                            f"｜quote_age {('%.0f' % qa) + 'ms' if qa is not None else 'n/a'}｜market_time={q['market_time']}")
                else:
                    info = "⚠ 解析不到价格"
            elif name.startswith("stock-state"):
                q = parse_stock_state(r.data)
                info = f"price {q['price']}｜时间 {hmd(q['ts'])}" if q else "⚠ 解析不到价格（字段名可能不同）"
            elif name.startswith("gex-levels"):
                lv = parse_levels(r.data)
                if lv:
                    tm = lv["time"]
                    info = (f"flip {lv['flip']}｜nearby_flips {lv['flips']}｜call {lv['call']}｜put {lv['put']}｜"
                            f"magnet {lv['magnet']}｜source={lv['source']}｜快照 {hmd(tm)} ET（距现在 {fmt_age((now_u - tm).total_seconds()) if tm else 'n/a'}）")
                else:
                    info = "⚠ 解析失败"
            elif name.startswith("net-prem-ticks"):
                tk = parse_ticks(r.data)
                if tk:
                    sg = sigma_from_ticks(tk)
                    info = (f"{len(tk)}个tick｜{hmd(tk[0]['t'])}→{hmd(tk[-1]['t'])} ET｜全天 Call净 {money(sum(t['ncp'] for t in tk), True)} "
                            f"Put净 {money(sum(t['npp'] for t in tk), True)}｜每分钟(call净−put净)σ={money(sg) if sg else 'n/a'}｜末tick距现在 {fmt_age((now_u - tk[-1]['t']).total_seconds())}")
                else:
                    info = "⚠ 无tick或解析失败"
            elif name == "flow-alerts":
                items = parse_flow(r.data, today) or []
                raw_list = unwrap(r.data)
                raw_list = raw_list.get("data", raw_list) if isinstance(raw_list, dict) else raw_list
                keys = sorted(raw_list[0].keys()) if isinstance(raw_list, list) and raw_list and isinstance(raw_list[0], dict) else []
                info = f"{len(items)}条（解析成功）"
                if items:
                    big = sorted(items, key=lambda x: -x["prem"])[:3]
                    info += f"｜最新 {hmd(items[-1]['tdt'])} ET｜前3大：" + "；".join(
                        f"{(x['type'] or '?')[:1].upper()}{x['strike']:g} {x['dte']}DTE {money(x['prem'])} {x['side']}→{x['sign']:+d}" for x in big if x['strike'] is not None)
                if keys:
                    info += f"\n   字段：{', '.join(keys)}"
            elif name == "greek-exposure":
                g = parse_greek(r.data)
                info = (f"日期 {g['date']}｜净gamma {g['net']:.3g}｜净占比 {g['ratio'] * 100:+.0f}%" if g else "⚠ 解析失败")
        except Exception as e:  # noqa: BLE001
            info = f"⚠ 解析异常 {type(e).__name__}"
        lines_ok.append(f"✅ {name}｜HTTP 200｜{r.ms}ms\n   {info}".rstrip())
        sample = r.data
        lines_shape.append(f"▸ {name}\n   结构：{shape(sample)[:500]}")
    try:  # 大单频率统计：单独再拉一次（500 条上限、7 天窗口），仅用于校准阈值
        r = uw.get("/api/option-trades/flow-alerts",
                   {"ticker_symbol": sym, "limit": 500, "min_premium": int(cfg.print_min)}, retries=1)
        if r.ok:
            lines_ok.append(flow_rate_report(parse_flow(r.data, today) or [], cfg))
        else:
            lines_ok.append(f"❌ 大单频率统计｜HTTP {r.status}｜{(r.err or '')[:140]}")
    except Exception as e:  # noqa: BLE001
        lines_ok.append(f"⚠ 大单频率统计异常 {type(e).__name__}")
    lim = getattr(uw, "limits", None) or {}
    lim_t = (f"额度头：limit={lim.get('limit')} count={lim.get('count')}" if lim
             else "额度头：无（符合 Basic 套餐“无每日请求上限”）")
    head = (f"🔬 UW 探测报告 · {now.astimezone(ET).strftime('%a %m-%d %H:%M')} ET｜{n_ok}/{len(tests)} 项可用\n"
            f"（非交易时段时，价格/点位/资金流是上一交易日的数据，属正常）\n{lim_t}")
    msgs, cur = [], head
    for ln in lines_ok:
        if len(cur) + len(ln) + 2 > 3600:
            msgs.append(cur)
            cur = ""
        cur += ("\n" if cur else "") + ln
    msgs.append(cur)
    cur = "🔬 字段结构（给开发者核对用）"
    for ln in lines_shape:
        if len(cur) + len(ln) + 2 > 3600:
            msgs.append(cur)
            cur = ""
        cur += ("\n" if cur else "") + ln
    msgs.append(cur)
    for m in msgs:
        if tg.send(m, silent=False) is None:
            log("探测报告发送失败：", tg.last_error)


def run_tgtest(cfg: Cfg, tg: Telegram, sleep=time.sleep) -> None:
    mid = tg.send("✅ UW 监控 · Telegram 推送测试\n这条消息稍后会被自动编辑（模拟“实时面板”原地刷新）。", silent=False)
    if mid is None:
        log("发送失败：", tg.last_error)
        raise SystemExit(1)
    sleep(2)
    r = tg.edit(mid, "✅ UW 监控 · Telegram 推送测试\n这条消息已被编辑 → 面板“原地刷新”功能正常。")
    log("编辑结果：", r)
    tg.send("🔕 这是一条静音消息（应当没有提示音）", silent=True)
    log("测试完成。")


def main() -> None:
    cfg = Cfg()
    SECRETS.extend([cfg.uw_key, cfg.tg_token, cfg.tg_chat])
    missing = [n for n, v in (("TELEGRAM_BOT_TOKEN", cfg.tg_token), ("TELEGRAM_CHAT_ID", cfg.tg_chat)) if not v]
    if cfg.mode != "telegram-test" and not cfg.uw_key:
        missing.append("UW_API_KEY")
    if missing:
        log("缺少以下 Secret（Settings → Secrets and variables → Actions）：" + ", ".join(missing))
        sys.exit(1)
    tg = Telegram(cfg.tg_token, cfg.tg_chat)
    if cfg.mode == "telegram-test":
        run_tgtest(cfg, tg)
        return
    uw = UW(cfg.uw_key)
    if cfg.mode == "probe":
        run_probe(cfg, uw, tg)
        return
    run_monitor(cfg, uw, tg)


if __name__ == "__main__":
    try:
        main()
    except SystemExit:
        raise
    except Exception as exc:  # noqa: BLE001
        print(safe(f"运行出错：{type(exc).__name__}: {exc}"), file=sys.stderr)
        sys.exit(1)
