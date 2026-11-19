# -*- coding: utf-8 -*-
"""
SPY 期权结构 + 资金流 实时监控（Unusual Whales API）→ Telegram
====================================================================

四种运行模式（由环境变量 MODE 控制，Actions 页面 Run workflow 时可选择）：
  monitor        正式监控：美股常规时段内每 15 秒轮询一次，维护"实时面板"（同一条 Telegram 消息原地刷新、静音）；
                 只在"共振"（结构/动量/资金流 ≥2 类同向）或关键结构事件、巨额单时才推送带提示音的消息；15:55 ET 发收盘摘要
                 （摘要里含"今日提醒复盘"：每条提醒按提醒价入场的现货收益）。每条推送都会记入 uw_state.json 的 journal，供回测使用。
  probe          接口探测：逐个调用 UW 接口，把状态码、字段结构、解析结果和大单频率统计发到 Telegram（首次部署用）；
                 另有"新数据流检查"：0DTE 按行权价 gamma、Greek flow、NOPE、成交量价位、按行权价盘中流向 是否可用、数据口径、最远能往回查多久。
  telegram-test  推送测试：发一条消息再编辑它，验证 Bot 与"原地刷新"功能。
  backtest       研究报告（依次发三条：结论页 → 要点页 → 附录；只有结论页带提示音），每一项给出 🟢有线索 / ⚪没看出优势 / 🟡样本不足 / ➖没测 / ⚠读不到 的标记：
                 ① 提醒入场：内置样本（2026-11-17 的 11 条提醒）+ journal 里记录的真实提醒，用 SPY 分钟线和 0DTE 平值期权的分钟成交价，
                    算"提醒后马上入场"在 +5/+15/+30/+60 分钟和 15:55 的收益、60 分钟内最好/最差收益（含滑点）；
                 ② 大单买卖标签：偏多标签（买Call/卖Put）之后 SPY 是不是比偏空标签之后涨得多（"多空差"，基本抵消当天趋势）；
                 ③ Greek flow（全部到期 / 当天到期）与 NOPE：近 15 分钟的方向性 delta 流，能不能领先之后 5/15/30/60 分钟的 SPY 涨跌（秩相关 + 噪声范围 + 按天一致性）；
                 ④ 前一日成交量价位（POC / 价值区上下沿）：价格第一次碰到之后，反弹得比"平移后的假价位"更多吗；
                 ⑤ 0DTE 按行权价 gamma：历史接口只给当天最后一个快照，回测会带入未来信息，所以只说明原因、不测。
                 环境变量：BT_FLOW_DAYS（回看几个交易日，默认 5；0 = 只跑 ① 提醒回测）、BT_STREAM_SECONDS（③④ 取数据的时间预算，默认 540 秒）。
                 回测只检验"信号有没有预测力"，不改变面板和提醒的任何逻辑。

信号三类（同向 ≥2 类才算"共振"）：
  结构   价格"确认"穿过 Flip 区（持续 60 秒）/ 确认突破 Call Wall、Put Wall（持续 45 秒）；
         Flip 迁移、墙位同向移动只作为辅助证据。墙位按行权价的 OI gamma 取近端峰值；离现价不足 0.1% 的大持仓行权价
         视为"磁吸位"、不当作墙（价格钉在它上面时不会反复报突破），价格从远处走近某堵墙时才锁定它
  动量   快速异动（20 分钟内幅度，阈值随当日波动自适应）/ 破位后继续延伸（每 0.2%）/ 价格里程碑
  资金流 近 10 分钟净权利金（call 净 − put 净）异常偏离（z 分数）、同向大单合计、单笔巨额单；
         大单在面板里按"买Call／卖Put／买Put／卖Call"拆开显示（含全天累计）

防噪音：Flip 用"区间 + 随波动自适应的缓冲 + 持续确认"，来回震荡时自动降级；共振有冷却时间；
同一波行情只在升级或明显延续时才再次提醒；"新信号"和"延续/升级提醒"各有每日带提示音上限（超出自动转静音）。
常用阈值（uw_monitor.yml 里列出的那些）可在 GitHub 仓库 Settings → Secrets and variables → Actions → Variables 里
新建同名变量来调整；其余阈值也都读同名环境变量，在 uw_monitor.yml 的 env 里照样子加一行即可。
本脚本与旧的 FlashAlpha 版完全独立：文件名、工作流、状态文件（uw_state.json）都不同，互不影响。

注意：本脚本不会在日志里打印任何密钥；Telegram / UW 的报错信息会先做脱敏。
仅为描述性提示，不构成任何交易建议。
"""
from __future__ import annotations

import bisect
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
STATE_VERSION = 4
STATE_FILE = os.environ.get("STATE_FILE", "uw_state.json")
DISCLAIMER = "⚠ 描述性提示，非交易建议"
SRC_LABEL = {"oi": "OI口径", "vol": "成交口径"}
CAP_LABEL = {"quote": "实时价格", "state": "备用价格", "lv_primary": "点位(OI)", "lv_live": "点位(盘中)", "ticks": "净权利金",
             "flow": "大单提醒", "greek": "日度Gamma", "strikes": "按行权价墙位", "ticks_prev": "前一日资金流基线"}

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
        # 墙位算法：strike = 按行权价的 OI gamma 自己算"近端墙"（默认）；uw = 直接用 UW gex-levels 给的墙。
        # 原因：UW 的 OI 口径 Put Wall 定义为"现价下方净 gamma 最大的行权价"，实测会落在 629（离现价 16%），盘中用不上；
        # 按行权价算出的近端墙实测在现价下方 0.7%~1.3%、上方 1.4% 左右。取不到按行权价的数据时自动退回 UW 的墙。
        self.wall_mode = s("WALL_MODE", "strike").lower()
        self.strike_every = f("STRIKE_EVERY_SECONDS", 300)     # OI 日内基本不变，5 分钟刷新一次足够
        self.strike_window_pct = f("STRIKE_WINDOW_PCT", 6.0)    # 只取现价 ±6% 内的行权价
        self.wall_sig = f("WALL_SIGNIFICANCE", 0.6)             # 近端墙的 gamma 需 ≥ 同侧最大值的 60%
        # 离现价不足 0.1%（SPY≈730 时约 0.73 美元，即价格几乎贴在这个行权价上）的行权价是"磁吸位"，不当作墙，
        # 否则价格在它上下晃几下就会反复报"突破"；但价格从远处走近某堵墙时，这堵墙会被锁定，之后照常判断突破（见 pick_walls）
        self.wall_min_pct = f("WALL_MIN_PCT", 0.10)
        self.wall_roll_pct = f("WALL_ROLL_PCT", 0.5)            # 已锁定的墙：价格越过它 0.5% 以上才换到下一道墙（期间仍按"已突破"处理）

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
        self.tide_min_ticks = int(f("TIDE_MIN_TICKS", 20))
        self.tide_open_guard = f("TIDE_OPEN_GUARD_MIN", 20)   # 开盘后头 N 分钟成交最密，只显示不触发资金流信号
        self.print_min = f("PRINT_MIN_PREMIUM", 250000)
        # 实测 SPY 一天约 330~390 笔 ≥$25万 的大单提醒（中位数约 $50万）：10 分钟同向合计 $300 万~$600 万是家常便饭。
        # 真实回放：周一（偏活跃的下跌日）≥$1000 万 4 次、≥$1500 万 0 次；周五（清淡）≥$800 万 0 次 → 取 $1000 万，约 0~4 次/天
        self.print_burst = f("PRINT_BURST_PREMIUM", 10000000)
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
        self.run_cap = int(f("RUN_PUSH_CAP", 6))                   # 已有信号的“延续/升级”提醒：单独的每日上限；两类上限超出后都自动转静音

        # 数据健康
        self.stale_price_s = f("STALE_PRICE_SECONDS", 90)
        self.outage_s = f("OUTAGE_SECONDS", 180)

        # 回测（MODE=backtest）：入场 = 提醒之后的下一根 1 分钟线的开盘价（再加 bt_delay_min 分钟模拟你的反应时间）；
        # 期权 = 同方向、最接近平值的 0DTE 合约，买入/卖出各扣 bt_slip 美元/股（SPY 平值 0DTE 点差通常 0.01~0.03；1 张合约 = 100 股）
        self.bt_slip = f("BT_SLIPPAGE", 0.03)
        self.bt_delay_min = f("BT_DELAY_MIN", 0)
        self.bt_kinds = [x.strip() for x in s("BT_KINDS", "conf,single,mega").split(",") if x.strip()]
        self.bt_seed = b("BT_SEED", True)             # 是否包含内置的 2026-11-17 样本
        self.bt_flow_days = int(f("BT_FLOW_DAYS", 5))  # "大单分类回测"回看最近几个交易日；0 = 不做
        self.bt_deep = f("BT_DEEP_DELTA", 0.6)        # |delta| ≥ 此值视为"深实值"
        self.bt_stream_s = f("BT_STREAM_SECONDS", 540)  # 新数据流检验（Greek flow / NOPE / 价值区）的时间预算（秒）；用完就只用已取到的天数


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


# 大单按"买/卖 × Call/Put"拆开：成交在 ask 侧算买、bid 侧算卖，买卖混合/方向不明归入 unclear。
# 买Call、卖Put = 偏多；买Put、卖Call = 偏空。
MIX_LABEL = (("buy_call", "买Call"), ("sell_put", "卖Put"), ("buy_put", "买Put"), ("sell_call", "卖Call"), ("unclear", "方向不明"))
MIX_BULL, MIX_BEAR = ("buy_call", "sell_put"), ("buy_put", "sell_call")


def mix_key(typ, side) -> str:
    if typ in ("call", "put") and side in ("ask", "bid"):
        return f"{'buy' if side == 'ask' else 'sell'}_{typ}"
    return "unclear"


def mix_add(mix: dict, typ, side, prem) -> None:
    m = mix.setdefault(mix_key(typ, side), [0.0, 0])
    m[0] += prem
    m[1] += 1


def print_mix(items) -> dict:
    mix: dict = {}
    for x in items:
        mix_add(mix, x.get("type"), x.get("side"), x["prem"])
    return mix


def mix_text(mix: dict, keys=None) -> str:
    """{"buy_call": [权利金合计, 笔数], …} → "买Call $9.1M（3笔）｜卖Put $3.2M（2笔）"；只列有数据的项。"""
    parts = [f"{label} {money(mix[k][0])}（{mix[k][1]}笔）" for k, label in MIX_LABEL if k in mix and (keys is None or k in keys)]
    return "｜".join(parts)


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
                    "size": num(r.get("total_size")),
                    # 以下仅供回测的"大单分类研究"使用（实盘引擎不读）：到期日、是否全为开仓、是否含多腿、未平仓量
                    "expiry": str(expiry)[:10] if expiry else None, "opening": bool(r.get("all_opening_trades")),
                    "multileg": bool(r.get("has_multileg")), "oi": num(r.get("open_interest"))})
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


def pick_walls(rows, spot, cfg: Cfg, prev=None):
    """按行权价的 OI gamma 选"近端墙"。
    Call Wall：现价上方、call gamma 集中度 ≥ 同侧最大值×wall_sig 且为局部峰值的最近行权价；Put Wall：对称。
    同时返回同侧"最大墙"（集中度最大的行权价）。数据不足返回 None；某一侧无候选则该侧为 None。
    三条规则：
    ① 离现价不足 wall_min_pct 的行权价不当作墙——价格正钉在大持仓行权价上时，它是"磁吸位"，不是要"突破"的墙
       （当成墙，价格在它上下晃几下就会反复报突破）；墙改选更远的一道。
    ② 锁定：prev = {"call": 上一轮的 Call Wall, "put": 上一轮的 Put Wall}（某一侧的突破已确认就不要传，让墙立刻让位给下一道）。
       价格从远处走近某堵墙时，这堵墙已被选中并锁定；之后价格靠近它（进入 wall_min_pct 以内）、甚至刚越过它时仍保留，
       直到价格越过它 wall_roll_pct 以上才换到下一道墙。否则墙会在价格靠近时消失，突破就无从判断。
    ③ 同一个行权价若同时被选为 Call Wall 和 Put Wall，它只算价格"另一侧"的那堵墙。
    rows 来自 parse_strike_gamma：[{strike, c_oi, p_oi, ...}]（call gamma 为正、put gamma 为负，取绝对值比较）。"""
    if not rows or not spot or len(rows) < 8:
        return None
    roll = cfg.wall_roll_pct / 100.0
    near = cfg.wall_min_pct / 100.0
    prev = prev or {}
    pts_by = {kind: {r["strike"]: abs(r[key]) for r in rows if r.get(key) is not None}
              for kind, key in (("call", "c_oi"), ("put", "p_oi"))}
    orders = {kind: sorted(pts) for kind, pts in pts_by.items()}

    def is_peak(kind, k):
        pts, order = pts_by[kind], orders[kind]
        i = order.index(k)
        nb = [pts[order[j]] for j in range(max(0, i - 2), min(len(order), i + 3)) if j != i]
        return all(pts[k] >= x for x in nb)

    def choose(kind, exclude=()):
        pts = pts_by[kind]
        order = orders[kind]
        lock = prev.get(kind)
        if lock is not None:                            # 锁定的墙必须仍是这一侧有数据的行权价
            lock = next((k for k in order if abs(k - lock) < 1e-6 and pts[k] > 0), None)
        if kind == "call":
            far = lambda k: k >= spot * (1 + near)      # noqa: E731  在现价上方、且离现价够远
            held = lambda k: k >= spot * (1 - roll)     # noqa: E731  价格尚未越过它 roll 以上
        else:
            far = lambda k: k <= spot * (1 - near)      # noqa: E731
            held = lambda k: k <= spot * (1 + roll)     # noqa: E731
        # 候选 = 离现价够远的行权价 + 仍被锁定的墙（即使价格已走进 wall_min_pct 以内、或刚越过它）
        cand = [k for k in order if pts[k] > 0 and k not in exclude and (far(k) or (k == lock and held(k)))]
        if not cand:
            return None, None
        kmax = max(cand, key=lambda k: pts[k])
        gmax = pts[kmax]
        # 锁定墙只在"不够远"时才免于显著性检验（它被选中时已通过检验；数据小幅漂移不应让它在价格贴近时消失）
        sig = [k for k in cand if (k == lock and not far(k)) or (pts[k] >= cfg.wall_sig * gmax and is_peak(kind, k))]
        return ((min(sig) if kind == "call" else max(sig)) if sig else kmax), kmax

    out = {}
    for kind in ("call", "put"):
        out[kind], out[kind + "_max"] = choose(kind)
    if out["call"] is not None and out["call"] == out["put"]:
        k = out["call"]
        drop = "call" if spot >= k else "put"          # 价格在它上方 → 它是支撑（Put Wall）；在它下方 → 它是阻力（Call Wall）
        out[drop], _ = choose(drop, exclude=(k,))
    # 被当作"磁吸位"跳过的近处大持仓行权价（仅用于面板/探测显示，让人看得出为什么墙没落在它上面）
    pins = []
    gall = {kind: max(pts.values()) for kind, pts in pts_by.items() if pts}
    for k in sorted({k for pts in pts_by.values() for k in pts}):
        if abs(k - spot) >= spot * near or k in (out["call"], out["put"]):
            continue
        kinds = [nm for kind, nm in (("call", "Call"), ("put", "Put"))
                 if k in pts_by[kind] and kind in gall and pts_by[kind][k] >= cfg.wall_sig * gall[kind] and is_peak(kind, k)]
        if kinds:
            pins.append({"strike": k, "kinds": kinds})
    out["pins"] = sorted(pins, key=lambda p: abs(p["strike"] - spot))[:2]
    return out


def is_rth(dt) -> bool:
    """是否在美股常规交易时段（9:30–16:00 ET）。UW 的资金流 tick 从 7:30 到 16:15，盘前盘后很清淡，不能混进波动基线。"""
    e = dt.astimezone(ET)
    m = e.hour * 60 + e.minute
    return 9 * 60 + 30 <= m < 16 * 60


def minutes_since_open(dt) -> float:
    e = dt.astimezone(ET)
    return (e - e.replace(hour=9, minute=30, second=0, microsecond=0)).total_seconds() / 60.0


def tide_stats(ticks, now_u: datetime, window_min: float, sigma_prev, cfg: Cfg):
    """x = 每分钟(call 净权利金 − put 净权利金)，正=看多倾向。波动基线只用常规时段的 tick。"""
    xs = [(t["t"], t["ncp"] - t["npp"]) for t in ticks]
    cut = now_u - timedelta(minutes=window_min)
    recent = [x for (tt, x) in xs if tt > cut]
    past = [x for (tt, x) in xs if tt <= cut and is_rth(tt)]
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
    xs = [t["ncp"] - t["npp"] for t in ticks if is_rth(t["t"])]
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
        "pivot": None, "px_hist": [], "impulse_state": None, "breaks": [], "flip_cross_ts": [], "wall_cross_ts": {"call": [], "put": []},
        "zone": {"side": None, "pending": None, "last": None},
        "walls": {"call_ref": None, "put_ref": None, "pending": {"call": None, "put": None}},
        "broken": {"call": None, "put": None},
        "hist": {"primary": [], "live": []},
        "flags": {"migration": None, "wall_shift": None},
        "events": [], "day_events": [],
        "flow": {"seen": [], "items": [], "tide_state": None, "prints_state": None,
                 "sigma_prev": None, "sigma_prev_done": False, "day_mix": {}},
        "run": None, "last_push": {}, "outbox": [],
        "outage": {"since": None, "notified": False},
        "notified": {}, "digest_close": False, "greek": None,
        "counters": {"cycles": 0, "pushed": 0, "silent": 0, "sent": 0, "loud_capped": 0},
        "prev_price": None,
        "journal": [],      # 每条推送的提醒记录（跨日保留，供回测）：{t, k, d, p, s, x}
        "day_px": [],       # 当天每分钟最后一个价格 [[分钟起点 epoch 秒, 价格], ...]（供收盘复盘）
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
# 提醒复盘（收盘摘要用）：每条提醒按"提醒价"入场的现货收益
# ----------------------------------------------------------------------------
KIND_ICON = {"conf": "🔔", "conf_run": "🔁", "single": "⚡", "mega": "🐋"}
KIND_NAME = {"conf": "共振", "conf_run": "共振延续", "single": "结构", "mega": "巨额单"}


def alert_scorecard(alerts, day_px, horizons=(15, 30, 60)):
    """alerts：journal 记录（t/k/d/p）；day_px：[[分钟起点 epoch 秒, 该分钟最后价格], ...]。
    返回 (rows, skipped)：rows 每条含 +H 分钟和"到最后一个价格"的方向收益（%）、之后的最大有利/不利（按分钟价）；
    skipped = 方向不明（d 不是 up/down）而没计入的条数。数据还没走到的时间点记 None。"""
    rows, skipped = [], 0
    if not day_px:
        return rows, skipped
    ks = [x[0] for x in day_px]
    last_t, last_p = ks[-1], day_px[-1][1]
    for a in alerts:
        d, t, p = a.get("d"), parse_iso(a.get("t")), num(a.get("p"))
        if t is None or not p:
            continue
        if d not in ("up", "down"):
            skipped += 1
            continue
        sg, te = (1 if d == "up" else -1), t.timestamp()
        ret = {}
        for H in horizons:
            tt = te + H * 60
            i = bisect.bisect_right(ks, tt) - 1
            ret[H] = sg * (day_px[i][1] - p) / p * 100 if (tt <= last_t + 60 and i >= 0) else None
        path = [x[1] for x in day_px[bisect.bisect_right(ks, te):]]
        mfe = mae = last = None
        if path:
            fav = [sg * (q - p) / p * 100 for q in path]
            mfe, mae, last = max(max(fav), 0.0), min(min(fav), 0.0), sg * (last_p - p) / p * 100
        rows.append({"t": a["t"], "k": a.get("k"), "d": d, "p": p, "ret": ret, "last": last, "mfe": mfe, "mae": mae,
                     "silent": bool(a.get("s"))})
    return rows, skipped


def _agg(vals):
    v = [x for x in vals if x is not None]
    if not v:
        return 0, 0, None, None
    return len(v), sum(1 for x in v if x > 0), sum(v) / len(v), statistics.median(v)


def _pc(x, nd=2) -> str:
    return "—" if x is None else f"{x:+.{nd}f}%"


def scorecard_lines(rows, skipped, horizons=(15, 30, 60), max_rows=12) -> list:
    if not rows:
        return []
    L = ["📋 今日提醒复盘（按提醒价入场｜现货口径｜不含期权杠杆和点差；样本很少，仅供参考）"]
    parts = []
    for H in horizons:
        n, w, m, _ = _agg([r["ret"].get(H) for r in rows])
        if n:
            parts.append(f"+{H}分钟 赢{w}/{n} 均{m:+.2f}%")
    n, w, m, _ = _agg([r["last"] for r in rows])
    if n:
        parts.append(f"到摘要时 赢{w}/{n} 均{m:+.2f}%")
    L.append(f"共 {len(rows)} 条有方向" + (f"（另 {skipped} 条方向不明，未计入）" if skipped else "") + "｜" + "｜".join(parts))
    kinds = []
    for k in ("conf", "single", "mega"):
        sub = [r for r in rows if r["k"] == k]
        if sub:
            n, w, m, _ = _agg([r["last"] for r in sub])
            if n:
                kinds.append(f"{KIND_ICON[k]}{KIND_NAME[k]} {len(sub)}条 赢{w}/{n} 均{m:+.2f}%")
    if kinds:
        L.append("到摘要时按类型：" + "｜".join(kinds))
    for r in rows[-max_rows:]:
        r15, r60 = r["ret"].get(15), r["ret"].get(60)
        L.append(f"  {hm(parse_iso(r['t']))} {'▲' if r['d'] == 'up' else '▼'}{KIND_ICON.get(r['k'], '')} {r['p']:.2f}｜+15m {_pc(r15)}｜+60m {_pc(r60)}｜到摘要 {_pc(r['last'])}"
                 f"｜最大有利 {_pc(r['mfe'])} 最大不利 {_pc(r['mae'])}" + ("｜🔕静音" if r.get("silent") else ""))
    return L


# ----------------------------------------------------------------------------
# 引擎：逐周期更新信号 → 事件 → 共振 → 推送队列
# ----------------------------------------------------------------------------
class Engine:
    def __init__(self, cfg: Cfg, state: dict | None = None):
        self.cfg = cfg
        self.s = state if state else new_state("")
        self.s.setdefault("journal", [])        # 兼容旧状态文件（STATE_VERSION 不变）
        self.s.setdefault("day_px", [])
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

    def queue_push(self, now, kind, text, silent=False, P=None, d=None, brief=None):
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
        if P is not None and kind in ("conf", "single", "mega", "conf_run"):
            try:
                self.journal_add(now, kind, d, P, bool(silent), brief or text)
            except Exception:  # noqa: BLE001  记录失败绝不能影响推送
                pass

    def journal_add(self, now, kind, d, P, silent, text):
        """记录一条提醒（时间/类型/方向/提醒价/是否静音/摘要），跨日保留 120 天、最多 600 条；回测与收盘复盘都读它。"""
        first = (text or "").strip().splitlines()[0] if (text or "").strip() else ""
        j = self.s.setdefault("journal", [])
        j.append({"t": iso(now), "k": kind, "d": d, "p": round(float(P), 2), "s": bool(silent), "x": first[:80]})
        cut = now - timedelta(days=120)
        self.s["journal"] = [x for x in j if (parse_iso(x.get("t")) or now) >= cut][-600:]

    def reset_day(self, today: str):
        old = self.s
        self.s = new_state(today)
        self.s["notified"] = old.get("notified", {})
        self.s["outbox"] = old.get("outbox", [])
        self.s["greek"] = None
        self.s["journal"] = old.get("journal", [])

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
        dp = self.s.setdefault("day_px", [])          # 每分钟最后一个价格，收盘复盘用（约 390 条/天）
        m0 = int(ts // 60) * 60
        if dp and dp[-1][0] == m0:
            dp[-1][1] = round(P, 3)
        else:
            dp.append([m0, round(P, 3)])
            if len(dp) > 1000:
                del dp[: len(dp) - 1000]

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
                        name = "Call Wall" if kind == "call" else "Put Wall"
                        # 震荡保护：同一墙位在 chop_window_min 分钟内被"确认突破"达到 chop_crosses 次 → 视为来回震荡
                        ts = now.timestamp()
                        wc = self.s.setdefault("wall_cross_ts", {"call": [], "put": []})
                        allh = [x for x in wc.get(kind, []) if x[0] >= ts - cfg.chop_window_min * 60] + [[ts, lvl]]
                        wc[kind] = allh
                        tol = max(2 * buf, lvl * 0.0015)
                        same = [x for x in allh if abs(x[1] - lvl) <= tol]
                        chop = len(same) >= cfg.chop_crosses
                        self.s["broken"][kind] = {"level": lvl, "t": iso(now), "chop": chop}
                        text = (f"{name} {lvl:.2f} {'向上突破' if d == 'up' else '向下跌破'}已确认"
                                f"（现价 {P:.2f}，已越过 {abs(P - lvl):.2f}，持续 {held:.0f}秒）")
                        if chop:
                            text += (f"\n  ⚠ {cfg.chop_window_min:.0f}分钟内第{len(same)}次突破同一墙位，价格在墙位附近来回震荡，"
                                     f"可靠性较低（不计入结构确认）")
                        self.add_event(now, "wall_break", d, text, P, level=lvl, chop=chop)
                        if not chop:
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
            if it["prem"] >= cfg.print_min:                      # 全天累计：买/卖 × Call/Put（面板与收盘摘要用）
                mix_add(f.setdefault("day_mix", {}), it.get("type"), it.get("side"), it["prem"])
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
                mixt = mix_text(print_mix(win), MIX_BULL if cur == "up" else MIX_BEAR)
                self.add_event(now, "prints", cur,
                               f"大单偏{'多' if cur == 'up' else '空'}：近{cfg.print_window_min:.0f}分钟同向合计 {money(tot)}（{cnt}笔）"
                               + (f"｜{mixt}" if mixt else ""), P, prem=tot)
            f["prints_state"] = cur
        elif max(up, dn) < 0.5 * cfg.print_burst:
            f["prints_state"] = None
        self.view["prints"] = {"up": up, "dn": dn, "n_up": n_up, "n_dn": n_dn, "mix": print_mix(win)}

        # 每分钟净权利金（tide）
        ticks = snap.get("ticks")
        self.view["tide"] = None
        if ticks:
            tide = tide_stats(ticks, now_u, cfg.tide_window_min, f.get("sigma_prev"), cfg)
            self.view["tide"] = tide
            z = tide["z"]
            guarded = (not cfg.force_run) and minutes_since_open(now) < cfg.tide_open_guard
            if z is not None and not guarded:
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
                ok = True
                if br.get("chop"):                      # 震荡中的突破：只有价格已明显离开墙位才算
                    P = self.view.get("P")
                    ok = bool(P and ((P - br["level"]) if d == "up" else (br["level"] - P)) / P * 100 >= cfg.chop_clear_pct)
                if ok:
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
            self.queue_push(now, "conf" if kind == "new" else "conf_run", text, silent=False, P=P, d=d)
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
                    self.queue_push(now, "mega", self.build_simple(now, P, "🐋", f"{cfg.symbol} 巨额单", e["text"]), silent=False,
                                    P=P, d=d, brief=e["text"])
                continue
            if d in conf_dirs:
                continue
            if kind in ("flip_cross", "wall_break") and e.get("chop"):
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
                self.queue_push(now, "single", self.build_simple(now, P, "⚡", f"{cfg.symbol} {'结构' if kind in ('flip_cross', 'wall_break') else '信号'}事件", e["text"], note),
                                silent=False, P=P, d=d, brief=e["text"])

    # ---------- 文本构造 ----------
    def levels_lines(self, P) -> str:
        v = self.view
        prim = v.get("prim") or {}
        zone = self.s["zone"].get("last")
        a = [f"现价 {P:.2f}"]
        if zone:
            rng = f"（区 {zone['lo']:.2f}–{zone['hi']:.2f}）" if zone["hi"] - zone["lo"] >= 0.01 else ""
            a.append(f"Flip {zone['center']:.2f}{rng}")
        sm = v.get("wall_src") == "strike"
        b = [wall_text(prim, k, P, sm) for k in ("call", "put") if prim.get(k) is not None]
        if prim.get("magnet") is not None:
            b.append(f"磁吸 {prim['magnet']:.2f}（{prim['magnet'] - P:+.2f}）")
        src = SRC_LABEL.get(self.cfg.primary_src, self.cfg.primary_src)
        if sm:
            src += "｜墙位=按行权价OI Gamma近端峰值"
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
        dm = s["flow"].get("day_mix")
        if dm:
            L.append(f"全天大单（≥{money(cfg.print_min)}）：" + mix_text(dm))
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

    def build_review(self, now) -> str:
        """收盘后另发一条静音消息："今日提醒复盘"（每条提醒按提醒价入场的现货收益）。没有提醒或出错都返回空串。"""
        s = self.s
        try:
            todays = [x for x in (s.get("journal") or []) if x.get("k") in ("conf", "single", "mega")
                      and (parse_iso(x.get("t")) or now).astimezone(ET).strftime("%Y-%m-%d") == s["date"]]
            rows, skipped = alert_scorecard(todays, s.get("day_px") or [])
            lines = scorecard_lines(rows, skipped)
            return "\n".join(lines + [DISCLAIMER]) if lines else ""
        except Exception:  # noqa: BLE001
            return ""

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
                     "prim": snap.get("primary"), "live": snap.get("live"), "wall_src": snap.get("wall_src"), "tide": None, "prints": None,
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
                review = self.build_review(now)
                if review:
                    self.queue_push(now, "review", review, silent=True)

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
def wall_text(prim: dict, key: str, P: float, strike_mode: bool) -> str:
    """一行里的墙位：Call Wall 750.00（+9.76）；按行权价口径且"最大墙"离得较远时附带最大墙。"""
    nm = "Call Wall" if key == "call" else "Put Wall"
    t = f"{nm} {prim[key]:.2f}（{prim[key] - P:+.2f}）"
    mx = prim.get(key + "_max")
    if strike_mode and mx is not None and abs(mx - prim[key]) >= 0.5:
        t += f"［最大墙 {mx:g}］"
    return t


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
        sm = v.get("wall_src") == "strike"
        parts = [wall_text(prim, k, P, sm) for k in ("call", "put") if prim.get(k) is not None]
        if parts:
            L.append("｜".join(parts))
        if sm:
            uw_c, uw_p = prim.get("call_uw"), prim.get("put_uw")
            L.append(f"  墙位口径：按行权价 OI Gamma 取近端峰值（UW 自带：Call {fpx(uw_c)}／Put {fpx(uw_p)}）")
            pins = prim.get("pins") or []
            if pins:
                L.append(f"  近处大持仓（离现价<{cfg.wall_min_pct:g}%，按磁吸位处理、不当墙）："
                         + "、".join(f"{p['strike']:g}（{'/'.join(p['kinds'])}）" for p in pins))
        elif cfg.wall_mode == "strike":
            L.append("  墙位口径：按行权价数据暂不可用，暂用 UW 自带的 Call/Put Wall")
        if prim.get("magnet") is not None:
            L.append(f"磁吸位 {prim['magnet']:.2f}（{prim['magnet'] - P:+.2f}）")
    elif not prim:
        L.append("（点位数据暂不可用）")
    for kind, nm in (("call", "Call Wall"), ("put", "Put Wall")):
        br = s["broken"].get(kind)
        if br:
            L.append(f"已{'上破' if kind == 'call' else '下破'} {nm} {br['level']:.2f}（{hm(parse_iso(br['t']))}确认，未收复）"
                     + ("｜⚠ 震荡中，暂不计入结构" if br.get("chop") else ""))
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
    if pr and pr.get("mix"):
        L.append(f"大单（近{cfg.print_window_min:.0f}分钟，≥{money(cfg.print_min)}）：偏多 {money(pr['up'])}（{pr['n_up']}笔）｜偏空 {money(pr['dn'])}（{pr['n_dn']}笔）")
        L.append("  明细：" + mix_text(pr["mix"]))
    dm = s["flow"].get("day_mix")
    if dm and not v.get("force"):
        L.append(f"全天大单（≥{money(cfg.print_min)}）：" + mix_text(dm))
    recent_items = [x for x in s["flow"]["items"] if x["prem"] >= cfg.print_min][-3:]
    if recent_items:
        L.append("最近大单：")
    for it in recent_items:
        dte = it.get("dte")
        how = {"ask": "买入", "bid": "卖出"}.get(it.get("side"), "混合")
        strike = f"{it['strike']:g}" if it.get("strike") is not None else "?"
        L.append(f"  {hm(parse_iso(it['t']))} {(it.get('type') or '?').upper()} {strike} "
                 f"{'0DTE' if dte == 0 else (str(dte) + 'DTE' if dte is not None else '')} {money(it['prem'])} "
                 f"{how}→{ {1: '偏多', -1: '偏空', 0: '方向不明'}[it['sign']] }")
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
        L.append("⚠ 不可用接口：" + "、".join(CAP_LABEL.get(k, k) for k in bad))
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
        self.status: dict = {}            # 每个接口最近一次失败的 HTTP 状态码
        self.flow_newer_ok = True         # flow-alerts 的 newer_than 参数是否可用（被拒绝时自动降级为普通查询）
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
        self.status[name] = r.status
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
        snap["wall_src"] = "uw"
        if cfg.wall_mode == "strike" and snap["primary"] is not None and "strikes" not in self.disabled:
            px = qv["price"] if qv else (self.eng.view.get("P") or None)
            if px:
                if self.due("strikes", now, cfg.strike_every) or "strikes" not in self.cache:
                    w = cfg.strike_window_pct / 100.0
                    self.fetch("strikes", f"/api/stock/{sym}/spot-exposures/strike",
                               {"limit": 500, "min_strike": int(px * (1 - w)), "max_strike": int(px * (1 + w)) + 1},
                               parse_strike_gamma, now, retries=1)
                # 锁定：上一轮选中的墙（call_ref/put_ref）在价格走近时继续保留，避免墙在贴近时消失、突破无从判断。
                # 但这堵墙的突破一旦确认，就交给 broken 状态去跟踪，墙立刻让位给下一道——否则相邻的两堵墙会漏掉第二堵。
                lock = {}
                for kind in ("call", "put"):
                    ref, br = eng.s["walls"].get(f"{kind}_ref"), eng.s["broken"].get(kind)
                    if ref is not None and not (br and abs(br["level"] - ref) < 1e-6):
                        lock[kind] = ref
                pw = pick_walls(self.cache.get("strikes"), px, cfg, lock)
                if pw and (pw["call"] is not None or pw["put"] is not None):
                    lv = dict(snap["primary"])
                    lv["call_uw"], lv["put_uw"] = lv.get("call"), lv.get("put")
                    for k in ("call", "put"):
                        if pw[k] is not None:
                            lv[k] = pw[k]
                    lv["call_max"], lv["put_max"] = pw["call_max"], pw["put_max"]
                    lv["pins"] = pw.get("pins") or []
                    snap["primary"] = lv
                    snap["wall_src"] = "strike"
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
            base = {"ticker_symbol": sym, "limit": 100, "min_premium": int(cfg.print_min)}
            parser = lambda raw: parse_flow(raw, now.astimezone(ET).date())  # noqa: E731
            items = self.fetch("flow", "/api/option-trades/flow-alerts",
                               dict(base, newer_than=int(since.timestamp())) if self.flow_newer_ok else base,
                               parser, now)
            if items is None and self.flow_newer_ok and self.status.get("flow") in (400, 422):
                # newer_than 参数被拒绝：改用不带该参数的普通查询（靠 key 去重），而不是让整个大单功能停用
                self.flow_newer_ok = False
                self.disabled.pop("flow", None)
                self.errs.pop("flow", None)
                log("flow-alerts 不接受 newer_than，已降级为普通查询")
                items = self.fetch("flow", "/api/option-trades/flow-alerts", base, parser, now)
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
            if k == "strikes":
                snap["notices"]["cap_strikes"] = f"按行权价的墙位数据不可用（{v}），已改用 UW 自带的 Call/Put Wall（可能离现价较远）；其余功能不受影响。"
            else:
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


def replay_tide(ticks, cfg: Cfg, z_list=(2.5, 3.0, 3.5, 4.0)) -> dict:
    """在一个完整交易日的 tick 上回放 tide 规则（只用"当时已有"的数据估 σ，和实盘一致），返回 {z阈值: [(时刻, 方向, 净额, z), ...]}。"""
    tk = [t for t in ticks if is_rth(t["t"])]
    out = {z: [] for z in z_list}
    if len(tk) < cfg.tide_min_ticks + int(cfg.tide_window_min) + 5:
        return out
    stats = []
    for i in range(len(tk)):
        stats.append(tide_stats(tk[:i + 1], tk[i]["t"], cfg.tide_window_min, None, cfg))
    for z_thr in z_list:
        state = None
        for i, st in enumerate(stats):
            if minutes_since_open(tk[i]["t"]) < cfg.tide_open_guard or st["z"] is None:
                continue
            z, cur = st["z"], None
            if z >= z_thr and st["S"] >= cfg.tide_abs_min:
                cur = "up"
            elif z <= -z_thr and st["S"] <= -cfg.tide_abs_min:
                cur = "down"
            if cur:
                if cur != state:
                    out[z_thr].append((tk[i]["t"], cur, st["S"], z))
                state = cur
            elif abs(z) < z_thr * 0.6:
                state = None
    return out


def replay_prints(items, cfg: Cfg, bursts=(5e6, 8e6, 10e6, 15e6, 20e6)) -> dict:
    """在已拉取的大单提醒上回放"同向大单"规则，返回 {门槛: {日期: 触发次数}}（按 ET 日期，仅常规时段）。"""
    bursts = sorted({float(b) for b in bursts} | {float(cfg.print_burst)})
    by_day = {}
    for x in items:
        if x["prem"] >= cfg.print_min:
            by_day.setdefault(x["tdt"].astimezone(ET).date(), []).append(x)
    res = {b: {} for b in bursts}
    for d, xs in by_day.items():
        xs.sort(key=lambda x: x["tdt"])
        open_dt = datetime(d.year, d.month, d.day, 9, 30, tzinfo=ET)
        series = []
        for m in range(0, 391):
            t = open_dt + timedelta(minutes=m)
            lo = t - timedelta(minutes=cfg.print_window_min)
            w = [x for x in xs if lo < x["tdt"] <= t]
            series.append((sum(x["prem"] for x in w if x["sign"] > 0), sum(x["prem"] for x in w if x["sign"] < 0),
                           sum(1 for x in w if x["sign"] > 0), sum(1 for x in w if x["sign"] < 0)))
        for b in bursts:
            state, n = None, 0
            for up, dn, n_up, n_dn in series:
                cur = None
                if up >= b and n_up >= cfg.print_min_count and up >= cfg.print_dominance * dn:
                    cur = "up"
                elif dn >= b and n_dn >= cfg.print_min_count and dn >= cfg.print_dominance * up:
                    cur = "down"
                if cur:
                    if cur != state:
                        n += 1
                    state = cur
                elif max(up, dn) < 0.5 * b:
                    state = None
            res[b][d] = n
    return res


def tide_replay_report(ticks, cfg: Cfg) -> str:
    tk = [t for t in ticks if is_rth(t["t"])]
    if len(tk) < 100:
        return "ℹ️ 资金流回放：常规时段 tick 不足 100 个，跳过"
    day = tk[-1]["t"].astimezone(ET).date()
    tk = [t for t in tk if t["t"].astimezone(ET).date() == day]
    res = replay_tide(tk, cfg)
    parts = []
    for z, evs in res.items():
        times = "、".join(f"{hm(e[0])}{'多' if e[1] == 'up' else '空'}" for e in evs[:5])
        parts.append(f"z≥{z:g} → {len(evs)}次" + (f"（{times}{'…' if len(evs) > 5 else ''}）" if evs else ""))
    return (f"📈 资金流回放（{day}，{cfg.tide_window_min:.0f}分钟窗口｜|净额|≥{money(cfg.tide_abs_min)}｜开盘后{cfg.tide_open_guard:.0f}分钟起算｜当前 TIDE_Z={cfg.tide_z:g}）\n   "
            + "｜".join(parts))


def prints_replay_report(items, cfg: Cfg) -> str:
    res = replay_prints(items, cfg)
    days = sorted({d for per in res.values() for d in per})
    L = [f"📈 大单回放（≥{money(cfg.print_min)}的提醒，同向合计≥门槛＋≥{cfg.print_min_count}笔＋≥{cfg.print_dominance:g}倍于反向，窗口{cfg.print_window_min:.0f}分钟）"]
    for b, per in res.items():
        mark = "（当前默认）" if abs(b - cfg.print_burst) < 1 else ""
        L.append(f"   门槛 ≥{money(b)}{mark}：" + "｜".join(f"{d.strftime('%m-%d')} {per.get(d, 0)}次" for d in days))
    L.append("   （最早一天的数据可能不完整，仅供参考）")
    return "\n".join(L)


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


# ---- 扩展接口（监控暂未使用；探测时检查可用性与数据是否合理，为下一阶段功能做准备） ----
def _any_ts(v):
    """时间戳可能是 ISO 字符串，也可能是毫秒/秒数字；都按 UTC 解析，失败返回 None。"""
    if isinstance(v, str):
        return parse_iso(v) or _ts_from_ms(v)
    return _ts_from_ms(v)


def _data_rows(raw) -> list:
    d = unwrap(raw)
    if isinstance(d, dict):
        d = d.get("data", d)
    return [r for r in d if isinstance(r, dict)] if isinstance(d, list) else []


def parse_strike_gamma(raw):
    """/spot-exposures/strike → 按行权价升序的 [{strike, price, time, c_oi, p_oi, c_vol, p_vol}]；无可用行返回 None。"""
    best, floor = {}, datetime.min.replace(tzinfo=UTC)
    for r in _data_rows(raw):
        k = num(r.get("strike"))
        if k is None:
            continue
        row = {"strike": k, "price": num(r.get("price")), "time": _any_ts(r.get("time")),
               "c_oi": num(r.get("call_gamma_oi")), "p_oi": num(r.get("put_gamma_oi")),
               "c_vol": num(r.get("call_gamma_vol")), "p_vol": num(r.get("put_gamma_vol"))}
        old = best.get(k)
        if old is None or (row["time"] or floor) >= (old["time"] or floor):     # 同一行权价若有多个时间点，只保留最新的
            best[k] = row
    out = sorted(best.values(), key=lambda x: x["strike"])
    return out or None


def strike_walls(rows, ref, key: str):
    """传统意义的墙：现价之上 call gamma 绝对值最大的行权价 = Call Wall；现价之下 put gamma 绝对值最大的 = Put Wall。返回 (前3 call, 前3 put)。"""
    ck, pk = "c_" + key, "p_" + key
    ups = sorted(((abs(r[ck]), r["strike"]) for r in rows if r["strike"] >= ref and r.get(ck) is not None), reverse=True)
    dns = sorted(((abs(r[pk]), r["strike"]) for r in rows if r["strike"] <= ref and r.get(pk) is not None), reverse=True)
    return ups[:3], dns[:3]


def strike_gamma_report(rows, spot=None, cfg=None, uw_levels=None) -> str:
    if not rows:
        return "ℹ️ 按行权价 gamma：无数据"
    prices = sorted(r["price"] for r in rows if r.get("price"))
    ref = prices[len(prices) // 2] if prices else spot
    if not ref:
        return "ℹ️ 按行权价 gamma：缺少参考价，无法计算"
    ts = [r["time"] for r in rows if r.get("time")]
    ks = [r["strike"] for r in rows]
    when = f"｜快照 {hmd(min(ts))}～{hmd(max(ts))} ET" if ts else ""
    L = [f"🧱 按行权价 gamma（spot-exposures/strike｜{len(rows)}个行权价 {min(ks):g}–{max(ks):g}｜参考价 {ref:.2f}{when}）"]

    def signs(k):
        v = [r[k] for r in rows if r.get(k)]
        return f"正{sum(1 for x in v if x > 0)}/负{sum(1 for x in v if x < 0)}"

    L.append(f"   符号：call_gamma_oi {signs('c_oi')}｜put_gamma_oi {signs('p_oi')}（用来确认 put gamma 是否为负数）")

    def fmt(lst):
        return "｜".join(f"{k:g}({(k - ref) / ref * 100:+.1f}%) {money(v).replace('$', '')}" for v, k in lst) or "无"

    for key, name in (("oi", "OI口径"), ("vol", "成交口径")):
        ups, dns = strike_walls(rows, ref, key)
        L.append(f"   {name} Call Wall 前3：{fmt(ups)}")
        L.append(f"   {name} Put Wall 前3：{fmt(dns)}")
    if cfg is not None:
        pw = pick_walls(rows, spot or ref, cfg)
        if pw:
            def one(k):
                return "无" if k is None else f"{k:g}({(k - ref) / ref * 100:+.1f}%)"
            L.append(f"   ▶ 监控将使用的近端墙（OI口径）：Call {one(pw['call'])}｜Put {one(pw['put'])}｜最大墙 Call {one(pw['call_max'])}｜Put {one(pw['put_max'])}")
            if pw.get("pins"):
                L.append(f"   ▶ 近处大持仓（离现价<{cfg.wall_min_pct:g}%，按磁吸位处理、不当墙）："
                         + "、".join(f"{p['strike']:g}（{'/'.join(p['kinds'])}）" for p in pw["pins"]))
        else:
            L.append("   ▶ 近端墙：数据不足，监控将回退到 UW 自带的 Call/Put Wall")
        if uw_levels:
            L.append(f"   对照 UW 自带（OI口径）：Call {fpx(uw_levels.get('call'))}｜Put {fpx(uw_levels.get('put'))}")
    return "\n".join(L)


def parse_spot_series(raw):
    """/spot-exposures（分钟级）→ [{t, price, oi, vol, dir}]，按时间升序。"""
    out = []
    for r in _data_rows(raw):
        t = _any_ts(r.get("time"))
        if t is None:
            continue
        out.append({"t": t, "price": num(r.get("price")), "oi": num(r.get("gamma_per_one_percent_move_oi")),
                    "vol": num(r.get("gamma_per_one_percent_move_vol")), "dir": num(r.get("gamma_per_one_percent_move_dir"))})
    out.sort(key=lambda x: x["t"])
    return out or None


def spot_series_report(rows) -> str:
    if not rows:
        return "ℹ️ 分钟级 gamma 序列：无数据"
    last = rows[-1]
    d = [x["dir"] for x in rows if x["dir"] is not None]
    flips = sum(1 for a, b in zip(d, d[1:]) if a * b < 0)
    rng = f"{money(min(d)).replace('$', '')}～{money(max(d)).replace('$', '')}" if d else "n/a"
    f = lambda v: "n/a" if v is None else money(v, True).replace("$", "")  # noqa: E731
    return (f"📉 分钟级 gamma 序列（spot-exposures｜{len(rows)}行｜{hmd(rows[0]['t'])}→{hmd(rows[-1]['t'])} ET）\n"
            f"   最新：成交方向口径 {f(last['dir'])}｜成交口径 {f(last['vol'])}｜OI口径 {f(last['oi'])}｜当天方向口径区间 {rng}｜正负号切换 {flips} 次")


def parse_greek_flow(raw):
    """/greek-flow（分钟级 delta / vega 流向；也适用于按到期日的 /greek-flow/{expiry}）→ [{t, dd, dv, td, tv, odd, otd, vol, tx}]：
    dd/dv=方向性(dir) delta/vega 流，td/tv=总量，odd/otd=价外(OTM)的方向性/总 delta 流，vol=期权成交量，tx=成交笔数。"""
    out = []
    for r in _data_rows(raw):
        t = _any_ts(r.get("timestamp")) or _any_ts(r.get("time"))
        if t is None:
            continue
        out.append({"t": t, "dd": num(r.get("dir_delta_flow")), "dv": num(r.get("dir_vega_flow")),
                    "td": num(r.get("total_delta_flow")), "tv": num(r.get("total_vega_flow")),
                    "odd": num(r.get("otm_dir_delta_flow")), "otd": num(r.get("otm_total_delta_flow")),
                    "vol": num(r.get("volume")), "tx": num(r.get("transactions"))})
    out.sort(key=lambda x: x["t"])
    return out or None


def greek_flow_report(rows) -> str:
    if not rows:
        return "ℹ️ delta/vega 流向：无数据"
    rth = [x for x in rows if is_rth(x["t"])]

    def stat(k):
        v = [x[k] for x in rth if x[k] is not None]
        if len(v) < 5:
            return "n/a"
        return f"Σ{money(sum(v), True).replace('$', '')} σ{money(statistics.pstdev(v)).replace('$', '')}"

    return (f"🌊 delta/vega 流向（greek-flow｜{len(rows)}行，常规时段 {len(rth)} 行｜{hmd(rows[0]['t'])}→{hmd(rows[-1]['t'])} ET）\n"
            f"   方向性 delta 流 {stat('dd')}｜方向性 vega 流 {stat('dv')}｜总 delta 流 {stat('td')}（Σ=全天合计，σ=每分钟波动）")


def sample_fields(raw, n: int = 16) -> str:
    rows = _data_rows(raw)
    if not rows:
        return "（无数据行）"
    return f"{len(rows)}行｜字段：" + ", ".join(list(rows[0].keys())[:n]) + ("…" if len(rows[0]) > n else "")


def run_probe_extras(cfg: Cfg, uw: UW, price, now_u, uw_levels=None) -> list:
    """逐个检查扩展接口；每个接口独立 try，任何一个出错都不影响其余。返回要追加到报告里的行。"""
    sym = cfg.symbol
    out = []
    p = {"limit": 500}
    if price:
        p.update(min_strike=int(price * 0.94), max_strike=int(price * 1.06) + 1)
    specs = [
        ("按行权价 gamma", f"/api/stock/{sym}/spot-exposures/strike", p,
         lambda r: strike_gamma_report(parse_strike_gamma(r), price, cfg, uw_levels)),
        ("分钟级 gamma 序列", f"/api/stock/{sym}/spot-exposures", None,
         lambda r: spot_series_report(parse_spot_series(r))),
        ("delta/vega 流向", f"/api/stock/{sym}/greek-flow", None,
         lambda r: greek_flow_report(parse_greek_flow(r))),
        ("option-contracts", f"/api/stock/{sym}/option-contracts", {"limit": 3, "exclude_zero_dte": "false"}, sample_fields),
        ("interpolated-iv", f"/api/stock/{sym}/interpolated-iv", None, sample_fields),
    ]
    ok = 0
    for name, path, params, fmt in specs:
        try:
            r = uw.get(path, params, retries=1)
            log(f"probe(扩展) {name}: HTTP {r.status} {r.ms}ms")
            if not r.ok:
                out.append(f"❌ {name}｜HTTP {r.status}｜{(r.err or '')[:120]}")
                continue
            ok += 1
            txt = fmt(r.data)
            out.append(txt if txt.startswith(("🧱", "📉", "🌊")) else f"✅ {name}｜{txt}")
        except Exception as e:  # noqa: BLE001
            out.append(f"⚠ {name} 解析异常 {type(e).__name__}")
    out.insert(0, f"🧩 扩展接口检查（按行权价 gamma 用于计算墙位，其余为后续功能做准备）｜{ok}/{len(specs)} 项可用")
    return out


# ---- 新数据流探针：接口是否可用、返回什么、能往回查多久（研究报告用这些数据，字段含义以这里的实测为准） ----
def probe_depth(call_fn, today: date, offsets=(30, 90, 180, 365, 540, 730), sleep=time.sleep) -> str:
    """同一个接口往回试几个日期，看最远能查多久（取不到数据时再试前一个工作日，排除休市日）。"""
    parts = []
    for off in offsets:
        d = today - timedelta(days=off)
        while d.weekday() >= 5:
            d -= timedelta(days=1)
        res = f"{off}天?"
        for _attempt in range(2):
            r = call_fn(d)
            sleep(0.3)
            if not r.ok:
                res = f"{off}天❌{r.status}" + (f"({r.code[:30]})" if r.code else "")
                break
            if _data_rows(r.data):
                res = f"{off}天✅"
                break
            res = f"{off}天∅"
            d -= timedelta(days=1)
            while d.weekday() >= 5:
                d -= timedelta(days=1)
        parts.append(res)
    return "往回查：" + " ".join(parts) + "（∅ = 返回了但没有数据，可能休市）"


def _fmt_vals(vals: list, n: int = 3) -> str:
    return " ".join(f"{v:,.0f}" if abs(v) >= 100 else f"{v:.3g}" for v in vals[:n])


def probe_gamma_lines(raw) -> list:
    rows = _data_rows(raw)
    if not rows:
        return ["返回 0 行（结构见字段结构）"]
    agg: dict = {}
    for r in rows:
        k = num(r.get("strike"))
        if k is None:
            continue
        a = agg.setdefault(k, [0.0, 0.0])
        a[0] += num(r.get("call_gamma_oi")) or 0.0
        a[1] += num(r.get("put_gamma_oi")) or 0.0
    ts = [t for t in (_any_ts(r.get("time")) for r in rows) if t]
    px = sorted(x for x in (num(r.get("price")) for r in rows) if x)
    top = sorted(agg.items(), key=lambda kv: -(abs(kv[1][0]) + abs(kv[1][1])))[:5]
    when = f"｜快照 {hmd(min(ts))}→{hmd(max(ts))} ET" if ts else ""
    L = [f"{len(rows)} 行｜行权价 {min(agg):g}–{max(agg):g}（{len(agg)} 个）｜price {px[len(px) // 2]:g}{when}｜行内带 expiry 字段：{'是' if 'expiry' in rows[0] else '否'}"
         if agg else f"{len(rows)} 行，但读不到 strike"]
    if top:
        L.append("gamma(OI) 最大的 5 个行权价：" + "｜".join(f"{k:g}（C {money(c, True).replace('$', '')} / P {money(p, True).replace('$', '')}）" for k, (c, p) in top))
    return L


def probe_gf_lines(raw) -> list:
    rows = parse_greek_flow(raw)
    if not rows:
        return ["解析不到行（结构见字段结构）"]
    rth = [x for x in rows if is_rth(x["t"])]
    vals = [x["dd"] for x in rth if x["dd"] is not None]
    ac = lag1_autocorr(vals)
    how = "无法判定" if ac is None else ("当天累计值" if ac >= 0.9 else "逐分钟增量")
    L = [f"{len(rows)} 行（常规时段 {len(rth)}）｜{hmd(rows[0]['t'])}→{hmd(rows[-1]['t'])} ET｜dir_delta_flow 判定：{how}"
         + (f"（相邻自相关 {ac:.2f}）" if ac is not None else "")]
    if vals:
        mid = len(vals) // 2
        L.append(f"dir_delta_flow 前3/中3/末3：{_fmt_vals(vals)} ｜ {_fmt_vals(vals[mid:])} ｜ {_fmt_vals(vals[-3:])}"
                 f"｜合计 {sum(vals):,.0f}｜单分钟波动 σ {statistics.pstdev(vals):,.0f}")
    return L


def probe_nope_lines(raw) -> list:
    rows = parse_nope(raw)
    if not rows:
        return ["解析不到行（结构见字段结构）"]
    rth = [x for x in rows if is_rth(x["t"])]

    def mono(k):
        v = [x[k] for x in rth if x[k] is not None]
        if len(v) < 10:
            return "n/a"
        return f"{100.0 * sum(1 for a, b in zip(v, v[1:]) if b >= a) / (len(v) - 1):.0f}%"

    nf = [x["nf"] for x in rth if x["nf"] is not None]
    nn = [x["nope"] for x in rth if x["nope"] is not None]
    L = [f"{len(rows)} 行（常规时段 {len(rth)}）｜{hmd(rows[0]['t'])}→{hmd(rows[-1]['t'])} ET"]
    L.append(f"nope_fill 首/末 {nf[0]:.4g}/{nf[-1]:.4g}｜nope 首/末 {nn[0]:.4g}/{nn[-1]:.4g}" if nf and nn else "nope / nope_fill 读不到数值")
    L.append(f"逐行不下降的比例（≈100% = 当天累计值）：call_vol {mono('cv')}｜put_vol {mono('pv')}｜stock_vol {mono('sv')}｜call_delta {mono('cd')}")
    return L


def probe_levels_lines(a_key: str, b_key: str, a_name: str, b_name: str):
    def f(raw) -> list:
        lv = parse_price_levels(raw, a_key, b_key)
        if not lv:
            return ["解析不到价位行（结构见字段结构）"]
        ta, tb = sum(x[1] for x in lv), sum(x[2] for x in lv)
        prof = volume_profile(lv)
        top = sorted(lv, key=lambda x: -(x[1] + x[2]))[:3]
        L = [f"{len(lv)} 个价位 {lv[0][0]:g}–{lv[-1][0]:g}｜{a_name} {ta / 1e6:.1f}M｜{b_name} {tb / 1e6:.1f}M｜合计 {(ta + tb) / 1e6:.1f}M"]
        if prof:
            L.append(f"POC {prof['poc']:.2f}｜价值区 {prof['val']:.2f}–{prof['vah']:.2f}（分箱 ${prof['bin']:.2f}）｜量最大的 3 个价位："
                     + "、".join(f"{p:g}({(a + b) / 1e6:.2f}M)" for p, a, b in top))
        return L
    return f


def probe_strike_flow_lines(raw) -> list:
    rows = _data_rows(raw)
    if not rows:
        return ["返回 0 行（结构见字段结构）"]
    ts = [t for t in (_any_ts(r.get("timestamp")) for r in rows) if t]
    ks = {num(r.get("strike")) for r in rows if num(r.get("strike")) is not None}
    tot: dict = {}
    for r in rows:
        k = num(r.get("strike"))
        if k is not None:
            tot[k] = tot.get(k, 0.0) + (num(r.get("call_premium")) or 0.0) + (num(r.get("put_premium")) or 0.0)
    top = sorted(tot.items(), key=lambda kv: -kv[1])[:5]
    when = f"｜{hmd(min(ts))}→{hmd(max(ts))} ET" if ts else ""
    L = [f"{len(rows)} 行｜{len(ks)} 个行权价{when}"]
    if top:
        L.append("权利金合计最大的 5 个行权价：" + "｜".join(f"{k:g} {money(v)}" for k, v in top))
    return L


def run_probe_streams(cfg: Cfg, uw, now, sleep=time.sleep) -> tuple:
    """新数据流逐个检查：能不能调用、返回几行/什么字段/数据口径、最远能往回查多久。返回 (报告行, 字段结构行)。"""
    sym = cfg.symbol
    day = recent_trading_days(now, 1)[0]
    today = now.astimezone(ET).date()
    state = {"fm": ["date", "iso"]}

    def gf0(x):
        r = None
        for fm in list(state["fm"]):
            exp = x.isoformat() if fm == "date" else f"{x.isoformat()}T00:00:00.000Z"
            r = uw.get(f"/api/stock/{sym}/greek-flow/{exp}", {"date": x.isoformat()}, retries=1)
            if r.ok or r.status not in (400, 404, 422):
                state["fm"] = [fm]
                return r
        return r

    g = lambda path, extra=None: (lambda x: uw.get(path, {"date": x.isoformat(), **(extra or {})}, retries=1))  # noqa: E731
    specs = [
        ("0DTE 按行权价 gamma", lambda x: uw.get(f"/api/stock/{sym}/spot-exposures/expiry-strike",
                                             {"expirations[]": x.isoformat(), "date": x.isoformat(), "limit": 500}, retries=1), probe_gamma_lines),
        ("Greek flow（全部到期）", g(f"/api/stock/{sym}/greek-flow"), probe_gf_lines),
        ("Greek flow（当天到期）", gf0, probe_gf_lines),
        ("NOPE", g(f"/api/stock/{sym}/nope"), probe_nope_lines),
        ("成交量价位·场内/场外", g(f"/api/stock/{sym}/stock-volume-price-levels"), probe_levels_lines("lit_vol", "off_vol", "场内(仅Nasdaq系)", "场外")),
        ("成交量价位·暗池", g(f"/api/darkpool/{sym}/price-levels"), probe_levels_lines("dark_pool_volume", "regular_volume", "暗池", "常规")),
        ("期权成交量按价位", g(f"/api/stock/{sym}/option/stock-price-levels"), probe_levels_lines("call_volume", "put_volume", "Call", "Put")),
        ("按行权价盘中流向", g(f"/api/stock/{sym}/flow-per-strike-intraday", {"filter": "Volume"}), probe_strike_flow_lines),
    ]
    out, shapes, n_ok = [], [], 0
    for name, call, summ in specs:
        try:
            r = call(day)
            sleep(0.4)
            log(f"probe(新数据流) {name}: HTTP {r.status} {r.ms}ms")
            if not r.ok:
                out.append(f"❌ {name}｜HTTP {r.status}｜{(r.err or '')[:120]}")
                continue
            n_ok += 1
            lines = summ(r.data)
            out.append(f"✅ {name}｜{lines[0]}")
            out.extend(f"   {x}" for x in lines[1:])
            out.append("   " + probe_depth(call, today, sleep=sleep))
            shapes.append(f"▸ {name}\n   结构：{shape(r.data)[:500]}")
        except Exception as e:  # noqa: BLE001
            out.append(f"⚠ {name} 检查异常 {type(e).__name__}")
    if state["fm"] != ["date", "iso"]:
        out.append(f"   （按到期日的 Greek flow：到期日写法 {'YYYY-MM-DD' if state['fm'] == ['date'] else '完整 ISO 时间'} 可用）")
    out.insert(0, f"🧪 新数据流检查（查询日期 {day}，即最近一个交易日）｜{n_ok}/{len(specs)} 项可用")
    return out, shapes


def run_probe(cfg: Cfg, uw: UW, tg: Telegram, now_fn=now_et) -> None:
    now = now_fn()
    sym = cfg.symbol
    today = now.astimezone(ET).date()
    prev = prev_weekdays(today, 1)[0].isoformat()
    now_u = now.astimezone(UTC)
    probe_price = None
    probe_levels = None
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
    probe_ticks = None
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
                    probe_price = q["price"]
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
                if lv and name == "gex-levels oi":
                    probe_levels = lv
                if lv:
                    tm = lv["time"]
                    info = (f"flip {lv['flip']}｜nearby_flips {lv['flips']}｜call {lv['call']}｜put {lv['put']}｜"
                            f"magnet {lv['magnet']}｜source={lv['source']}｜快照 {hmd(tm)} ET（距现在 {fmt_age((now_u - tm).total_seconds()) if tm else 'n/a'}）")
                else:
                    info = "⚠ 解析失败"
            elif name.startswith("net-prem-ticks"):
                tk = parse_ticks(r.data)
                if tk and name == "net-prem-ticks":
                    probe_ticks = tk
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
            fitems = parse_flow(r.data, today) or []
            lines_ok.append(flow_rate_report(fitems, cfg))
            if fitems:
                lines_ok.append(prints_replay_report(fitems, cfg))
                cutoff = max(x["tdt"] for x in fitems) - timedelta(minutes=30)     # 验证实盘用的 newer_than 参数是否有效
                r2 = uw.get("/api/option-trades/flow-alerts",
                            {"ticker_symbol": sym, "limit": 100, "min_premium": int(cfg.print_min),
                             "newer_than": int(cutoff.timestamp())}, retries=1)
                if r2.ok:
                    its = parse_flow(r2.data, today) or []
                    okf = all(x["tdt"] >= cutoff - timedelta(seconds=2) for x in its)
                    rng = f"{hmd(min(x['tdt'] for x in its))}→{hmd(max(x['tdt'] for x in its))}" if its else "-"
                    lines_ok.append(f"{'✅' if (its and okf) else '⚠'} newer_than 参数测试｜返回 {len(its)} 条｜{rng}｜"
                                    + ("全部晚于截止时间，过滤有效" if okf else "含早于截止时间的记录，过滤可能无效"))
                else:
                    lines_ok.append(f"❌ newer_than 参数测试｜HTTP {r2.status}｜{(r2.err or '')[:140]}")
        else:
            lines_ok.append(f"❌ 大单频率统计｜HTTP {r.status}｜{(r.err or '')[:140]}")
    except Exception as e:  # noqa: BLE001
        lines_ok.append(f"⚠ 大单频率统计异常 {type(e).__name__}")
    if probe_ticks:
        try:
            lines_ok.append(tide_replay_report(probe_ticks, cfg))
        except Exception as e:  # noqa: BLE001
            lines_ok.append(f"⚠ 资金流回放异常 {type(e).__name__}")
    try:
        lines_ok.extend(run_probe_extras(cfg, uw, probe_price, now_u, probe_levels))
    except Exception as e:  # noqa: BLE001
        lines_ok.append(f"⚠ 扩展接口检查异常 {type(e).__name__}")
    try:
        ok_l, shape_l = run_probe_streams(cfg, uw, now)
        lines_ok.extend(ok_l)
        lines_shape.extend(shape_l)
    except Exception as e:  # noqa: BLE001
        lines_ok.append(f"⚠ 新数据流检查异常 {type(e).__name__}")
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


# ----------------------------------------------------------------------------
# 回测（MODE=backtest）：① 提醒后"马上入场"的收益  ② 大单分类（买Call/卖Put/买Put/卖Call）之后的 SPY 涨跌
# ----------------------------------------------------------------------------
# 2026-11-17 当天实际收到的 11 条提醒（来自 Telegram 记录；时间为 ET，价格为消息里的"现价"；
# 最后一项 True = 当时已超过当日响铃上限，是静音推送）。d：up=偏多 / down=偏空。
SEED_ALERTS = [
    ("2026-11-17", "09:33", "mega", "down", 738.16, False),
    ("2026-11-17", "09:39", "mega", "up", 738.17, False),
    ("2026-11-17", "10:19", "mega", "down", 736.51, False),
    ("2026-11-17", "10:33", "conf", "down", 734.93, False),
    ("2026-11-17", "10:35", "single", "down", 734.16, False),
    ("2026-11-17", "10:42", "mega", "up", 731.28, False),
    ("2026-11-17", "11:01", "conf", "up", 732.21, True),
    ("2026-11-17", "11:42", "single", "down", 729.93, True),
    ("2026-11-17", "14:28", "mega", "up", 731.38, True),
    ("2026-11-17", "14:50", "single", "down", 729.94, True),
    ("2026-11-17", "15:00", "conf", "down", 728.36, True),
]
LABEL_SIGN = {"buy_call": 1, "sell_put": 1, "buy_put": -1, "sell_call": -1}


def seed_journal() -> list:
    out = []
    for day, hhmm, k, d, p, silent in SEED_ALERTS:
        y, mo, dd = (int(v) for v in day.split("-"))
        h, m = (int(v) for v in hhmm.split(":"))
        out.append({"t": iso(datetime(y, mo, dd, h, m, 0, tzinfo=ET)), "k": k, "d": d, "p": p, "s": silent,
                    "x": "内置样本", "seed": True})
    return out


def osi_symbol(root: str, day: date, cp: str, strike: float) -> str:
    """OSI 期权代码，如 SPY261117P00735000（根代码 + YYMMDD + C/P + 行权价×1000 补满 8 位）。"""
    return f"{root}{day.strftime('%y%m%d')}{cp}{int(round(strike * 1000)):08d}"


def et_day(ts) -> date:
    return datetime.fromtimestamp(ts, ET).date()


def session_epochs(day: date):
    """(开盘 09:30, 回测收盘点 15:55, 收盘 16:00) 的 epoch 秒。"""
    f = lambda h, m: datetime(day.year, day.month, day.day, h, m, tzinfo=ET).timestamp()  # noqa: E731
    return f(9, 30), f(15, 55), f(16, 0)


def parse_bars(raw) -> list:
    """UW 的 1 分钟数据（股票 OHLC / 期权 intraday）→ [{t: 分钟起点 epoch 秒, o, h, l, c}]，按时间升序；缺关键字段的行丢弃。"""
    rows = unwrap(raw)
    if not isinstance(rows, list):
        return []
    out = {}
    for r in rows:
        if not isinstance(r, dict):
            continue
        t = parse_iso(r.get("start_time") or r.get("timestamp") or r.get("time"))
        if t is None:
            continue
        o, h, l, c, a = (num(r.get(k)) for k in ("open", "high", "low", "close", "avg_price"))
        ref = next((x for x in (o, c, a) if x is not None), None)
        if ref is None:
            continue
        o = ref if o is None else o
        c = o if c is None else c
        h = max(o, c) if h is None else h
        l = min(o, c) if l is None else l
        out[t.timestamp()] = {"t": t.timestamp(), "o": o, "h": h, "l": l, "c": c}
    return [out[k] for k in sorted(out)]


class BarSeries:
    """按时间排序的分钟线；价格一律取"某分钟起点的开盘价"，缺这一分钟就沿用之前最后一笔成交价（太旧则视为没有）。"""

    def __init__(self, bars):
        self.bars = bars
        self.ts = [b["t"] for b in bars]

    def first_at_or_after(self, t, max_gap_s):
        i = bisect.bisect_left(self.ts, t)
        if i >= len(self.bars) or self.bars[i]["t"] - t > max_gap_s:
            return None
        return i

    def price_at(self, t, max_stale_s=600.0):
        i = bisect.bisect_left(self.ts, t)
        if i < len(self.ts) and self.ts[i] == t:
            return self.bars[i]["o"]
        j = i - 1
        if j >= 0 and t - self.ts[j] <= max_stale_s:
            return self.bars[j]["c"]
        return None

    def window(self, t0, t1):
        return self.bars[bisect.bisect_left(self.ts, t0):bisect.bisect_left(self.ts, t1)]


def sim_track(ser: BarSeries, t_alert: float, sg: int, delay_min: float, close_t: float, slip: float = 0.0,
              opt: bool = False, horizons=(5, 15, 30, 60), max_entry_gap_s: float = 300.0):
    """模拟"提醒后马上入场"：入场 = 提醒之后的下一根分钟线开盘价（再加 delay_min 分钟）。
    现货（opt=False）：收益 = 方向 sg × 涨跌幅；期权（opt=True，只做多头）：成本 = 入场价 + slip，
    收益 = (出场价 − slip − 成本) / 成本。出场 = 入场后 +H 分钟（不得晚于 close_t）或 close_t。
    返回 {t0, entry, cost, ret{H}, close, mfe, mae}（mfe/mae = 入场后 60 分钟内最大有利/不利，%）；无法入场返回 None。"""
    te = (math.floor(t_alert / 60.0) + 1) * 60.0 + delay_min * 60.0
    i = ser.first_at_or_after(te, max_entry_gap_s)
    if i is None:
        return None
    t0, e = ser.bars[i]["t"], ser.bars[i]["o"]
    if t0 >= close_t or e <= 0:
        return None
    cost = e + slip if opt else e

    def ret_at(tt):
        x = ser.price_at(tt)
        if x is None:
            return None
        return (x - slip - cost) / cost * 100.0 if opt else sg * (x - e) / e * 100.0

    out = {"t0": t0, "entry": e, "cost": cost, "ret": {}}
    for H in horizons:
        tt = t0 + H * 60.0
        out["ret"][H] = ret_at(tt) if tt <= close_t else None
    out["close"] = ret_at(close_t)
    seg = ser.window(t0, min(t0 + 3600.0, close_t))
    out["mfe"] = out["mae"] = None
    if seg:
        hi, lo = max(b["h"] for b in seg), min(b["l"] for b in seg)
        if opt:
            out["mfe"], out["mae"] = (hi - slip - cost) / cost * 100.0, (lo - slip - cost) / cost * 100.0
        elif sg > 0:
            out["mfe"], out["mae"] = (hi - e) / e * 100.0, (lo - e) / e * 100.0
        else:
            out["mfe"], out["mae"] = (e - lo) / e * 100.0, (e - hi) / e * 100.0
    return out


def fetch_spy_bars(uw, cfg: Cfg, day: date, sleep=time.sleep):
    """取某一天的 1 分钟线（常规时段）。UW 文档没写清 date / end_date 的行为，所以依次试几种参数写法，取返回该日 K 线最多的一种。"""
    d_s = day.strftime("%Y-%m-%d")
    o_t, _c, e_t = session_epochs(day)
    variants = (("end_date+1D", {"end_date": d_s, "timeframe": "1D", "limit": 2500}),
                ("date", {"date": d_s, "limit": 2500}),
                ("end_date", {"end_date": d_s, "limit": 2500}))
    best, diag = [], []
    for name, params in variants:
        r = uw.get(f"/api/stock/{cfg.symbol}/ohlc/1m", params, retries=1)
        sleep(0.3)
        if not r.ok:
            diag.append(f"{name} HTTP {r.status} {(r.err or '')[:90]}".strip())
            if r.status in (401, 402, 403):          # 权限 / 历史范围问题：换参数没用
                break
            continue
        bars = [b for b in parse_bars(r.data) if o_t <= b["t"] < e_t]
        diag.append(f"{name} {len(bars)}根" + (f"（返回结构：{shape(r.data)[:120]}）" if not bars else ""))
        if len(bars) > len(best):
            best = bars
        if len(best) >= 380:
            break
    return best, diag


def fetch_option_bars(uw, osi: str, day: date, sleep=time.sleep):
    """取某个期权合约某天的 1 分钟成交数据。返回 (bars, 错误说明或 None)。"""
    d_s = day.strftime("%Y-%m-%d")
    r = uw.get(f"/api/option-contract/{osi}/intraday", {"date": d_s}, retries=1)
    sleep(0.3)
    if not r.ok:
        return [], f"{osi} HTTP {r.status} {(r.err or '')[:100]}".strip()
    bars = [b for b in parse_bars(r.data) if et_day(b["t"]) == day]
    if not bars:
        return [], f"{osi} 返回 0 根（结构：{shape(r.data)[:120]}）"
    return bars, None


def collect_alerts(cfg: Cfg, state_path: str) -> list:
    """回测样本 = journal（实盘自动记录）+ 内置的 11-17 样本；只留有方向的、类型在 BT_KINDS 里的；同一分钟同类型同方向只算一条。"""
    seen, out = set(), []

    def add(a, src):
        t, p = parse_iso(a.get("t")), num(a.get("p"))
        if t is None or not p or a.get("d") not in ("up", "down") or a.get("k") not in cfg.bt_kinds:
            return
        key = (t.astimezone(ET).strftime("%Y-%m-%d %H:%M"), a.get("k"), a.get("d"))
        if key in seen:
            return
        seen.add(key)
        out.append({**a, "tt": t.timestamp(), "p": p, "src": src})

    try:
        st = load_state(state_path)
    except Exception:  # noqa: BLE001
        st = {}
    for a in (st.get("journal") or []):
        add(a, "journal")
    if cfg.bt_seed:
        for a in seed_journal():
            add(a, "seed")
    out.sort(key=lambda x: x["tt"])
    return out


def run_alert_backtest(cfg: Cfg, uw, alerts: list, series_for, sleep=time.sleep):
    results, opt_cache = [], {}
    days = sorted({et_day(a["tt"]) for a in alerts})
    for a in alerts:
        day = et_day(a["tt"])
        _o, close_t, _e = session_epochs(day)
        sg = 1 if a["d"] == "up" else -1
        res = {"a": a}
        ser = series_for(day)
        if ser is None:
            res["err"] = "没有取到当天的 SPY 分钟线"
        else:
            res["spot"] = sim_track(ser, a["tt"], sg, cfg.bt_delay_min, close_t)
            if res["spot"] is None:
                res["err"] = "提醒太靠近收盘或分钟线缺失，无法入场"
        cp = "C" if sg > 0 else "P"
        strike = float(math.floor(a["p"] + 0.5))                    # 最接近平值的整数行权价
        osi = osi_symbol(cfg.symbol, day, cp, strike)
        res["osi"], res["lab"] = osi, f"{cp}{strike:g}"
        if osi not in opt_cache:
            opt_cache[osi] = fetch_option_bars(uw, osi, day, sleep)
        bars, err = opt_cache[osi]
        if bars:
            res["opt"] = sim_track(BarSeries(bars), a["tt"], 1, cfg.bt_delay_min, close_t, slip=cfg.bt_slip, opt=True)
            if res["opt"] is None:
                res["opt_err"] = "提醒后 5 分钟内该合约没有成交，无法入场"
        else:
            res["opt_err"] = err
        results.append(res)
    return results, days


def _po(x) -> str:
    if x is None:
        return "—"
    return f"{x:+.0f}%" if abs(x) >= 10 else f"{x:+.1f}%"


def build_backtest_report(cfg: Cfg, results: list, days: list) -> list:
    """附录A：提醒回测的完整统计（+5/+15/+30/+60 分钟、15:55、60 分钟内最好/最差）和逐条明细。要点见研究报告的"提醒入场"。"""
    HZ = (5, 15, 30, 60)
    L = [f"📊 附录A｜提醒回测明细（{len(results)} 条提醒｜{days[0]}～{days[-1]}）",
         "入场：提醒之后的下一根 1 分钟线开盘价" + (f"，再延后 {cfg.bt_delay_min:g} 分钟" if cfg.bt_delay_min else "")
         + "；出场：入场后 +5/+15/+30/+60 分钟，或 15:55",
         f"现货：按提醒方向做多/做空 SPY｜期权：同方向、最接近平值的 0DTE（买 Call 或买 Put），买入和卖出各扣 ${cfg.bt_slip:.2f}/股滑点，未含手续费"]

    def block(title, tracks, fmt):
        L.append(title)
        if not tracks:
            L.append("  （没有可用数据）")
            return
        for h in HZ:
            n, w, m, md = _agg([t["ret"].get(h) for t in tracks])
            if n:
                L.append(f"  +{h}分钟：赢 {w}/{n}｜平均 {fmt(m)}｜中位 {fmt(md)}")
        n, w, m, md = _agg([t["close"] for t in tracks])
        if n:
            L.append(f"  到15:55：赢 {w}/{n}｜平均 {fmt(m)}｜中位 {fmt(md)}")
        mf = [t["mfe"] for t in tracks if t.get("mfe") is not None]
        ma = [t["mae"] for t in tracks if t.get("mae") is not None]
        if mf and ma:
            L.append(f"  入场后60分钟内：最大有利均值 {fmt(sum(mf) / len(mf))}｜最大不利均值 {fmt(sum(ma) / len(ma))}")

    spot = [r["spot"] for r in results if r.get("spot")]
    opt = [r["opt"] for r in results if r.get("opt")]
    block(f"【现货 SPY｜可回测 {len(spot)}/{len(results)} 条】", spot, _pc)
    block(f"【期权 0DTE 平值｜可回测 {len(opt)}/{len(results)} 条｜含滑点】", opt, _po)
    kinds = []
    for k in ("conf", "single", "mega"):
        sub = [r for r in results if r["a"]["k"] == k]
        if not sub:
            continue
        sp = _agg([(r.get("spot") or {}).get("ret", {}).get(60) for r in sub])
        op = _agg([(r.get("opt") or {}).get("ret", {}).get(60) for r in sub])
        kinds.append(f"  {KIND_ICON[k]}{KIND_NAME[k]} {len(sub)}条｜现货+60m 赢{sp[1]}/{sp[0]} 均{_pc(sp[2])}｜期权+60m 赢{op[1]}/{op[0]} 均{_po(op[2])}")
    if kinds:
        L.append("【按类型（+60分钟）】")
        L.extend(kinds)
    L.append("【逐条】（🔕=当时已超过响铃上限、是静音推送）")
    for r in results:
        a = r["a"]
        when = datetime.fromtimestamp(a["tt"], ET).strftime("%m-%d %H:%M")
        tag = f"{'▲' if a['d'] == 'up' else '▼'}{KIND_ICON.get(a['k'], '')}{'🔕' if a.get('s') else ''}"
        sp, op = r.get("spot"), r.get("opt")
        s_txt = f"现货60m {_pc(sp['ret'].get(60))}" if sp else "现货无数据"
        if op:
            rr = op["ret"]
            L.append(f"{when} {tag} {r['lab']}@{op['entry']:.2f}｜15m {_po(rr.get(15))}｜30m {_po(rr.get(30))}｜60m {_po(rr.get(60))}"
                     f"｜15:55 {_po(op['close'])}｜60分钟内最好 {_po(op['mfe'])} 最差 {_po(op['mae'])}｜{s_txt}")
        else:
            L.append(f"{when} {tag} {r['lab']} 期权无数据（{(r.get('opt_err') or r.get('err') or '')[:70]}）｜{s_txt}")
    L.append("提示：「最好/最差」= 入场后60分钟内曾到过的最高/最低收益（不代表你一定能在那个价位成交）；1 张合约 = 100 股；"
             "期权用的是成交价而不是买卖报价，实际点差可能更大；样本很少，仅供参考。")
    return L


def fetch_flow_history(uw, cfg: Cfg, t_start: float, t_end: float, sleep=time.sleep, max_pages: int = 14):
    """从 t_end 往前翻页取 flow-alerts（每页 500 条，older_than = 本页最早一条的时间），直到越过 t_start。返回 (按时间升序的列表, 诊断)。"""
    rows, diag, cursor = {}, [], t_end
    for page in range(max_pages):
        params = {"ticker_symbol": cfg.symbol, "limit": 500, "min_premium": int(cfg.print_min),
                  "newer_than": int(t_start), "older_than": int(cursor)}
        r = uw.get("/api/option-trades/flow-alerts", params, retries=1)
        sleep(0.3)
        if not r.ok:
            diag.append(f"flow-alerts 第{page + 1}页 HTTP {r.status} {(r.err or '')[:90]}".strip())
            break
        items = parse_flow(r.data, date.today()) or []
        if not items:
            diag.append(f"flow-alerts 第{page + 1}页 0条")
            break
        fresh = [x for x in items if x["key"] not in rows]
        for x in items:
            rows[x["key"]] = x
        diag.append(f"flow-alerts 第{page + 1}页 {len(items)}条（新增{len(fresh)}）")
        oldest = items[0]["tdt"].timestamp()
        if len(items) < 500 or oldest <= t_start or not fresh:
            break
        cursor = oldest
    out = [x for x in rows.values() if t_start <= x["tdt"].timestamp() <= t_end]
    out.sort(key=lambda x: x["tdt"])
    return out, diag


def flow_study_rows(items: list, series_for, horizons=(5, 15, 30, 60)) -> list:
    """每条大单：分类 + 它生成后（下一分钟开盘价起）SPY 的涨跌幅（原始涨跌，不按方向调整）。开盘前 5 分钟和收盘前 5 分钟的不看。"""
    rows = []
    for it in items:
        te = it["tdt"].timestamp()
        day = et_day(te)
        ser = series_for(day)
        if ser is None:
            continue
        o_t, c_t, _e = session_epochs(day)
        if te < o_t + 300 or te > c_t - 300:
            continue
        tr = sim_track(ser, te, 1, 0.0, c_t, horizons=horizons)
        if not tr:
            continue
        dte = None
        if it.get("expiry"):
            try:
                dte = (date.fromisoformat(it["expiry"]) - day).days
            except ValueError:
                dte = None
        rows.append({"day": day, "cat": mix_key(it.get("type"), it.get("side")), "prem": it["prem"],
                     "delta": it.get("delta"), "opening": bool(it.get("opening")), "multileg": bool(it.get("multileg")),
                     "dte": dte, "r": tr["ret"]})
    return rows


DTE_BUCKETS = ("0DTE", "1–5天", "6–30天", "30天+", "未知")


def dte_bucket(dte) -> str:
    """到期天数分档：0DTE / 1–5 天 / 6–30 天 / 30 天以上；取不到到期日 = 未知。"""
    if dte is None:
        return "未知"
    if dte <= 0:
        return "0DTE"
    if dte <= 5:
        return "1–5天"
    if dte <= 30:
        return "6–30天"
    return "30天+"


def _study_stats(rows: list, H: int) -> dict:
    mv = [r["r"].get(H) for r in rows if r["r"].get(H) is not None]
    lab = [r["r"][H] * LABEL_SIGN[r["cat"]] for r in rows if r["cat"] in LABEL_SIGN and r["r"].get(H) is not None]
    return {"n": len(mv), "nl": len(lab), "mv": (sum(mv) / len(mv)) if mv else None,
            "lab": (sum(lab) / len(lab)) if lab else None,
            "win": (100.0 * sum(1 for x in lab if x > 0) / len(lab)) if lab else None}


def _pw(x) -> str:
    return "—" if x is None else f"{x:.0f}%"


FLOW_TIERS = (250_000, 500_000, 1_000_000, 5_000_000)       # 金额档（累计）：≥25万 / ≥50万 / ≥100万 / ≥500万


def flow_matrix_lines(cfg: Cfg, rows: list, kind: str) -> list:
    """金额档 × 到期档：买入型（kind="buy"）或卖出型（"sell"）、非深实值、非多腿的大单，之后 5/15/30 分钟的
    标签收益、胜率、多空差。金额档是累计的（≥50万 包含 ≥100万、≥500万 的那些），对应"如果门槛设在这里，会看到什么"。
    到期档 = 0DTE / 1–5天 / 6–30天 / 30天+（日历天数）。每天 = 平均每天条数（按样本里有数据的天数算）。n<10 不统计。"""
    up_cat, dn_cat = ("buy_call", "buy_put") if kind == "buy" else ("sell_put", "sell_call")
    base = [r for r in rows if r["cat"] in (up_cat, dn_cat) and not r["multileg"]
            and not (r["delta"] is not None and abs(r["delta"]) >= cfg.bt_deep)]
    ndays = len({r["day"] for r in rows}) or 1
    out = []
    for bucket in DTE_BUCKETS[:4]:
        grp = [r for r in base if dte_bucket(r["dte"]) == bucket]
        out.append(f"  到期 {bucket}")
        for v in FLOW_TIERS:
            sub = [r for r in grp if (r["prem"] or 0) >= v]
            n = len(sub)
            head = f"   ≥{v / 10000:g}万 n={n}（{n / ndays:.1f}/天）"
            if n < 10:
                out.append(head + "｜样本不足")
                continue
            lab, win = [], []
            for H in (5, 15, 30):
                st = _study_stats(sub, H)
                lab.append(f"{H}m {_pc(st['lab'])}")
                win.append(f"{H}m {_pw(st['win'])}")
            spread = "—"
            a, d = [r for r in sub if r["cat"] == up_cat], [r for r in sub if r["cat"] == dn_cat]
            if len(a) >= 5 and len(d) >= 5:
                x, y = _study_stats(a, 15)["mv"], _study_stats(d, 15)["mv"]
                if x is not None and y is not None:
                    spread = _pc(x - y)
            out.append(head + "｜标签收益 " + " ".join(lab) + "｜胜率 " + " ".join(win) + f"｜多空差15m {spread}")
    return out


def build_flow_study_report(cfg: Cfg, rows: list, days: list, n_items: int) -> list:
    """附录B：大单分类回测的完整明细（按类别、分层、金额档 × 到期档矩阵、按天）。要点见研究报告的"大单买卖标签"。"""
    L = [f"🔬 附录B｜大单分类回测明细（{days[0]}～{days[-1]}｜≥{money(cfg.print_min)} 的大单 {n_items} 条，可用 {len(rows)} 条）",
         "每条大单从生成后的下一分钟 SPY 开盘价算起，看之后 5/15/30/60 分钟 SPY 实际涨跌（%）。",
         "「标签收益」= 按买卖标签的多空方向调整后的涨跌（买Call/卖Put 当多，买Put/卖Call 当空）；注意它含大盘整体涨跌（见下面的基准），"
         "要看方向有没有用，应看\"多空区分度\"（两组相减，抵消了大盘涨跌）。"]
    base = {H: _study_stats(rows, H)["mv"] for H in (5, 15, 30, 60)}
    L.append("基准（所有大单时点的 SPY 平均涨跌）：" + "｜".join(f"+{H}m {_pc(base[H])}" for H in (5, 15, 30, 60)))

    # 到期分布：这些大单到底是多少天到期的（提醒目前没有到期日限制）
    def dte_dist(sub):
        cnt = {k: 0 for k in DTE_BUCKETS}
        prm = {k: 0.0 for k in DTE_BUCKETS}
        for r in sub:
            b = dte_bucket(r["dte"])
            cnt[b] += 1
            prm[b] += r["prem"] or 0.0
        return cnt, prm

    cnt, prm = dte_dist(rows)
    tot_n, tot_p = sum(cnt.values()), sum(prm.values())
    if tot_n:
        by_n = "｜".join(f"{k} {100.0 * cnt[k] / tot_n:.0f}%" for k in DTE_BUCKETS if cnt[k])
        by_p = "｜".join(f"{k} {100.0 * prm[k] / tot_p:.0f}%" for k in DTE_BUCKETS if prm[k]) if tot_p else "—"
        L.append(f"【到期分布】≥{money(cfg.print_min)} 大单 n={tot_n}｜按条数 {by_n}｜按权利金 {by_p}")
        big = [r for r in rows if (r["prem"] or 0) >= cfg.mega_min]
        if big:
            c2, _p2 = dte_dist(big)
            L.append(f"  其中 ≥{money(cfg.mega_min)} 的巨额单 n={len(big)}：" + "｜".join(f"{k} {c2[k]}条" for k in DTE_BUCKETS if c2[k]))
    L.append("【按类别】涨跌 = SPY 平均涨跌；标签 = 标签收益；胜 = 标签方向猜对的比例")
    for k, label in MIX_LABEL[:4]:
        sub = [r for r in rows if r["cat"] == k]
        if len(sub) < 5:
            continue
        parts = []
        for H in (15, 60):
            st = _study_stats(sub, H)
            parts.append(f"{H}m 涨跌 {_pc(st['mv'])} 标签 {_pc(st['lab'])} 胜{_pw(st['win'])}")
        L.append(f"  {label} n={len(sub)}｜" + "｜".join(parts))
    for a, b, name in (("buy_call", "buy_put", "买Call − 买Put"), ("sell_put", "sell_call", "卖Put − 卖Call")):
        sa, sb = [r for r in rows if r["cat"] == a], [r for r in rows if r["cat"] == b]
        if len(sa) >= 5 and len(sb) >= 5:
            ds = []
            for H in (15, 60):
                x, y = _study_stats(sa, H)["mv"], _study_stats(sb, H)["mv"]
                ds.append(f"{H}m {_pc(x - y) if x is not None and y is not None else '—'}")
            L.append(f"  多空区分度 {name}：" + "｜".join(ds) + "（>0 = “偏多”标签之后 SPY 涨得更多）")

    def is_buy(r):
        return r["cat"] in ("buy_call", "buy_put")

    def is_sell(r):
        return r["cat"] in ("sell_put", "sell_call")

    def deep(r):
        return r["delta"] is not None and abs(r["delta"]) >= cfg.bt_deep

    groups = [
        ("买入型·非深实值·非多腿", lambda r: is_buy(r) and not deep(r) and not r["multileg"]),
        ("买入型·深实值", lambda r: is_buy(r) and deep(r)),
        ("卖出型·非深实值·非多腿", lambda r: is_sell(r) and not deep(r) and not r["multileg"]),
        ("卖出型·深实值", lambda r: is_sell(r) and deep(r)),
        ("含多腿成交", lambda r: r["multileg"]),
        ("全为开仓", lambda r: r["opening"]),
        ("到期 0DTE", lambda r: dte_bucket(r["dte"]) == "0DTE"),
        ("到期 1–5天", lambda r: dte_bucket(r["dte"]) == "1–5天"),
        ("到期 6–30天", lambda r: dte_bucket(r["dte"]) == "6–30天"),
        ("到期 30天+", lambda r: dte_bucket(r["dte"]) == "30天+"),
        # 方案 B 里“只保留这一类做方向证据”的候选规则：买入型、非深实值、非多腿、5 天内到期
        ("候选规则·买入型·非深实值·非多腿·≤5天到期",
         lambda r: is_buy(r) and not deep(r) and not r["multileg"] and dte_bucket(r["dte"]) in ("0DTE", "1–5天")),
    ]
    L.append(f"【分层】（深实值 = |Δ|≥{cfg.bt_deep:g}；只列有方向标签的 ≥20 条）")
    for name, fn in groups:
        sub = [r for r in rows if fn(r)]
        s15, s60 = _study_stats(sub, 15), _study_stats(sub, 60)
        if s60["nl"] >= 20:
            L.append(f"  {name} n={s60['nl']}｜标签收益 15m {_pc(s15['lab'])} 60m {_pc(s60['lab'])}｜60m 胜{_pw(s60['win'])}")
    for kind, title, note in (
            ("buy", "买入型", "标签收益 = 买Call 算多、买Put 算空调整后的 SPY 涨跌；多空差 = 买Call 之后与买Put 之后 SPY 平均涨跌之差，>0 才说明方向有用"),
            ("sell", "卖出型", "卖Put 算多、卖Call 算空；标签收益≈0 或为负、多空差≤0，就说明卖出型不该当方向用")):
        L.append(f"【{title}·非深实值·非多腿｜金额档 × 到期档】（金额档累计；每天 = 平均每天条数；n<10 不统计）")
        L.append(f"  {note}")
        L.extend(flow_matrix_lines(cfg, rows, kind))
    for name, fn in (("买入型", is_buy), ("卖出型", is_sell)):
        per = []
        for day in days:
            st = _study_stats([r for r in rows if r["day"] == day and fn(r)], 60)
            if st["nl"] >= 10:
                per.append(f"{day:%m-%d} {_pc(st['lab'])}")
        if per:
            L.append(f"【{name} 60分钟标签收益·按天】" + "｜".join(per))
    L.append("提示：同一时段会连着出很多条大单，样本高度重叠，有效样本远小于条数；n 不到 30 的格子、只有几天的数据，只能当线索，不能当结论。")
    return L


# ----------------------------------------------------------------------------
# 研究报告（MODE=backtest）：结论先行 → 要点 → 附录
# 新数据流检验：Greek flow / NOPE 与之后 SPY 涨跌的领先-滞后关系；前一日成交量价位（POC / 价值区）能不能挡住价格
# 只做"信号有没有预测力"的检验，不改动面板和提醒的任何逻辑。
# ----------------------------------------------------------------------------
CHIP_OK, CHIP_FLAT, CHIP_THIN, CHIP_NA, CHIP_ERR = "🟢", "⚪", "🟡", "➖", "⚠"
EDGE_MIN_PCT = 0.03          # "多空差"（SPY 涨跌，%）至少要有这么大，才可能盖过 0DTE 期权的点差 + 时间损耗
MIN_STUDY_DAYS = 3           # 少于这么多天：一律"样本不足"
MIN_SIDE_N = 100             # 多、空每一侧至少这么多条大单，才对大单标签下结论
CONSISTENT = 0.8             # "按天一致"：至少 80% 的天与整体方向相同（且至少 4 天可比）
SIG_STEP_MIN, SIG_WINDOW_MIN = 5, 15       # 信号检验：每 5 分钟取一个观察点，信号 = 近 15 分钟的流向
BULL_CATS, BEAR_CATS = ("buy_call", "sell_put"), ("buy_put", "sell_call")
SIG_NAMES = {"gf_all": "Greek flow·全部到期", "gf_0dte": "Greek flow·当天到期(0DTE)", "nope": "NOPE（成交口径）"}


def sign_test_p(k: int, n: int) -> float:
    """按天符号检验（双侧）：n 天里有 k 天为正，如果正负纯属随机（各 50%），出现这么一边倒（或更甚）的概率。"""
    if n <= 0:
        return 1.0
    kk = max(k, n - k)
    tail = sum(math.comb(n, i) for i in range(kk, n + 1)) / float(2 ** n)
    return min(1.0, 2.0 * tail)


def _ranks(xs: list) -> list:
    idx = sorted(range(len(xs)), key=lambda i: xs[i])
    out = [0.0] * len(xs)
    i = 0
    while i < len(idx):
        j = i
        while j + 1 < len(idx) and xs[idx[j + 1]] == xs[idx[i]]:
            j += 1
        r = (i + j) / 2.0 + 1.0
        for k in range(i, j + 1):
            out[idx[k]] = r
        i = j + 1
    return out


def pearson(xs: list, ys: list):
    n = len(xs)
    if n < 3 or n != len(ys):
        return None
    mx, my = sum(xs) / n, sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    syy = sum((y - my) ** 2 for y in ys)
    if sxx <= 0 or syy <= 0:
        return None
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / math.sqrt(sxx * syy)


def spearman(xs: list, ys: list, min_n: int = 20):
    """秩相关（对极端值不敏感）。样本少于 min_n 返回 None。"""
    if len(xs) < min_n or len(xs) != len(ys):
        return None
    return pearson(_ranks(xs), _ranks(ys))


def lag1_autocorr(vals: list):
    """相邻两个数的相关：接近 1 = 这列数是"累计值"；接近 0 = 每分钟的独立增量。"""
    v = [x for x in vals if x is not None]
    if len(v) < 30:
        return None
    return pearson(v[:-1], v[1:])


def _cc(x) -> str:
    return "—" if x is None else f"{x:+.2f}"


# ---- 逐分钟数据（Greek flow / NOPE）→ 信号 ----
def parse_nope(raw):
    """/nope（逐分钟）→ [{t, nope, nf, cd, pd, cfd, pfd, cv, pv, sv}]，按时间升序；nf = nope_fill（用成交当时的 delta 算的 NOPE）。"""
    out = []
    for r in _data_rows(raw):
        t = _any_ts(r.get("timestamp")) or _any_ts(r.get("time"))
        if t is None:
            continue
        out.append({"t": t, "nope": num(r.get("nope")), "nf": num(r.get("nope_fill")),
                    "cd": num(r.get("call_delta")), "pd": num(r.get("put_delta")),
                    "cfd": num(r.get("call_fill_delta")), "pfd": num(r.get("put_fill_delta")),
                    "cv": num(r.get("call_vol")), "pv": num(r.get("put_vol")), "sv": num(r.get("stock_vol"))})
    out.sort(key=lambda x: x["t"])
    return out or None


class MinSeries:
    """一天里的逐分钟数据。ts = 每行的分钟起点（epoch 秒）；cum=True 表示这列数是"当天累计值"（取窗口内的增量要做差）。"""

    def __init__(self, rows: list, key: str, cum: bool = False):
        pairs = sorted((r["t"].timestamp(), r[key]) for r in rows if r.get("t") is not None and r.get(key) is not None)
        self.ts = [p[0] for p in pairs]
        self.vals = [p[1] for p in pairs]
        self.cum = cum

    def window(self, t_end: float, minutes: float, max_stale_s: float = 180.0):
        """t_end 之前（不含 t_end 这一分钟）最近 minutes 分钟的流量：增量序列 = 窗口内求和；累计序列 = 末值 − 窗口起点之前的值。
        窗口里没有数据、或最后一行离 t_end 太久（数据没跟上）→ None。"""
        i1 = bisect.bisect_left(self.ts, t_end)
        i0 = bisect.bisect_left(self.ts, t_end - minutes * 60.0)
        if i1 == 0 or t_end - self.ts[i1 - 1] > max_stale_s:
            return None
        if self.cum:
            return None if i0 == 0 else self.vals[i1 - 1] - self.vals[i0 - 1]
        return None if i1 <= i0 else sum(self.vals[i0:i1])


def signal_points(day: date, ser, sig_fn, step_min: int = SIG_STEP_MIN, window_min: int = SIG_WINDOW_MIN,
                  first_hm=(10, 0), last_hm=(15, 30), horizons=(5, 15, 30, 60)) -> list:
    """某一天的观察点（每 step_min 分钟一个）：x = sig_fn(t)（只能用 t 之前已走完的分钟）；
    f[H] = 从 t 起 H 分钟后 SPY 涨跌（%）；past = 之前 window_min 分钟的涨跌（%，用来看"流向是不是只在跟着价格走"）。"""
    _o, close_t, _e = session_epochs(day)
    t = datetime(day.year, day.month, day.day, first_hm[0], first_hm[1], tzinfo=ET).timestamp()
    t_last = datetime(day.year, day.month, day.day, last_hm[0], last_hm[1], tzinfo=ET).timestamp()
    pts = []
    while t <= t_last:
        x = sig_fn(t)
        p0 = ser.price_at(t)
        if x is not None and p0:
            pp = ser.price_at(t - window_min * 60.0)
            f = {}
            for H in horizons:
                p1 = ser.price_at(t + H * 60.0) if t + H * 60.0 <= close_t else None
                f[H] = (p1 / p0 - 1.0) * 100.0 if p1 else None
            pts.append({"day": day, "t": t, "x": x, "past": ((p0 / pp - 1.0) * 100.0) if pp else None, "f": f})
        t += step_min * 60.0
    return pts


def tercile_spread(pts: list, H: int):
    """信号最强的 1/3 减最弱的 1/3，之后 H 分钟 SPY 平均涨跌之差（%）；再按天算一遍（用整体的分界线），数有几天为正。"""
    use = [p for p in pts if p["f"].get(H) is not None]
    if len(use) < 30:
        return None
    xs = sorted(p["x"] for p in use)
    lo_c, hi_c = xs[len(xs) // 3], xs[(2 * len(xs)) // 3]
    if not hi_c > lo_c:
        return None
    hi = [p for p in use if p["x"] >= hi_c]
    lo = [p for p in use if p["x"] <= lo_c]
    if not hi or not lo:
        return None

    def mean(g):
        return sum(p["f"][H] for p in g) / len(g)

    pos = n = 0
    for d in sorted({p["day"] for p in use}):
        hd = [p for p in hi if p["day"] == d]
        ld = [p for p in lo if p["day"] == d]
        if len(hd) >= 4 and len(ld) >= 4:
            n += 1
            pos += 1 if mean(hd) - mean(ld) > 0 else 0
    return {"spread": mean(hi) - mean(lo), "n_hi": len(hi), "n_lo": len(lo), "day_pos": pos, "day_n": n}


def study_signal(pts: list, horizons=(5, 15, 30, 60), window_min: int = SIG_WINDOW_MIN) -> dict:
    """一个信号的完整检验：与"之前"涨跌的相关（跟随）、与"之后 H 分钟"涨跌的相关（领先）、强弱三分之一的涨跌差、按天一致性。
    noise = 相关系数的"噪声范围"（约 95%）：按"每天约 360/max(窗口,H) 个互不重叠的窗口"估算有效样本，样本重叠所以比点数少得多。"""
    days = sorted({p["day"] for p in pts})
    pp = [(p["x"], p["past"]) for p in pts if p.get("past") is not None]
    res = {"n": len(pts), "days": len(days), "past": spearman([a for a, _ in pp], [b for _, b in pp]), "h": {}}
    for H in horizons:
        use = [p for p in pts if p["f"].get(H) is not None]
        n_eff = max(1.0, len(days) * 360.0 / max(window_min, H))
        res["h"][H] = {"n": len(use), "corr": spearman([p["x"] for p in use], [p["f"][H] for p in use]),
                       "noise": 2.0 / math.sqrt(n_eff), "ts": tercile_spread(pts, H)}
    return res


def _consistent(pos: int, n: int, positive: bool) -> bool:
    if n < 4:
        return False
    return pos >= CONSISTENT * n if positive else pos <= (1.0 - CONSISTENT) * n


def signals_verdict(stats: dict) -> tuple:
    """stats = {信号名: study_signal 结果} → (标记, 一句话)。有线索的门槛：相关系数超出噪声范围 + 强弱三分之一的涨跌差 ≥ EDGE_MIN_PCT + 按天一致。"""
    if not stats:
        return CHIP_ERR, "读不到数据（见附录诊断）"
    days = max(s["days"] for s in stats.values())
    if days < MIN_STUDY_DAYS or max(s["n"] for s in stats.values()) < 100:
        return CHIP_THIN, f"只有 {days} 天的数据，样本不足，不下结论"
    hits, follow = [], []
    for name, s in stats.items():
        for H in (15, 60):
            h = s["h"].get(H)
            ts = h["ts"] if h else None
            if not h or h["corr"] is None or not ts:
                continue
            if abs(h["corr"]) >= h["noise"] and abs(ts["spread"]) >= EDGE_MIN_PCT and h["corr"] * ts["spread"] > 0 \
                    and _consistent(ts["day_pos"], ts["day_n"], ts["spread"] > 0):
                hits.append((abs(h["corr"]), name, H, h["corr"]))
        if s["past"] is not None and abs(s["past"]) >= 0.2:
            follow.append(name)
    if hits:
        _a, name, H, c = max(hits)
        way = "（反向：流向偏多之后反而跌）" if c < 0 else ""
        return CHIP_OK, (f"有线索：{len(hits)} 个检验过关，最强是 {SIG_NAMES.get(name, name)} 之后{H}分钟（相关 {_cc(c)}）{way}；"
                         "6 个里挑出来的，有运气成分，需更多天确认")
    tail = "；与之前涨跌明显相关，说明流向多半是在跟着价格走" if follow else ""
    return CHIP_FLAT, "领先性都在噪声范围内，看不出它能提前告诉你方向" + tail


def study_flow_signals(cfg: Cfg, uw, days: list, series_for, sleep, deadline: float, diag: list) -> dict:
    """Greek flow（全部到期 / 当天到期）和 NOPE：每天取逐分钟数据，每 5 分钟一个观察点，
    信号 = 近 15 分钟的方向性 delta 流（NOPE = 近 15 分钟的变化），对照之后 5/15/30/60 分钟 SPY 涨跌。"""
    sym = cfg.symbol

    def d_iso(d):
        return {"date": d.isoformat()}

    gf_all = fetch_stream_days(uw, "greek-flow", lambda d: uw.get(f"/api/stock/{sym}/greek-flow", d_iso(d), retries=1),
                               parse_greek_flow, days, sleep, deadline, diag)
    fmt = {"try": ["date", "iso"]}

    def gf0_call(d):
        r = None
        for fm in list(fmt["try"]):
            exp = d.isoformat() if fm == "date" else f"{d.isoformat()}T00:00:00.000Z"
            r = uw.get(f"/api/stock/{sym}/greek-flow/{exp}", d_iso(d), retries=1)
            if r.ok or r.status not in (400, 404, 422):
                fmt["try"] = [fm]
                return r
        return r

    gf_0 = fetch_stream_days(uw, "greek-flow(当天到期)", gf0_call, parse_greek_flow, days, sleep, deadline, diag)
    nope = fetch_stream_days(uw, "nope", lambda d: uw.get(f"/api/stock/{sym}/nope", d_iso(d), retries=1),
                             parse_nope, days, sleep, deadline, diag)
    pts: dict = {"gf_all": [], "gf_0dte": [], "nope": []}
    info: dict = {"gf_all": [], "gf_0dte": [], "nope": []}
    for d in sorted(days):
        ser = series_for(d)
        if ser is None:
            continue
        for name, store, key in (("gf_all", gf_all, "dd"), ("gf_0dte", gf_0, "dd"), ("nope", nope, "nf")):
            rows = [r for r in (store.get(d) or []) if et_day(r["t"].timestamp()) == d and is_rth(r["t"])]
            if name == "nope" and rows and sum(1 for r in rows if r.get("nf") is not None) < len(rows) / 2:
                key = "nope"                                         # nope_fill 大多缺失 → 退回 nope
            if len(rows) < 200:
                if store.get(d) is not None:
                    diag.append(f"{SIG_NAMES[name]} {d:%m-%d}：常规时段只有 {len(rows)} 行，跳过")
                continue
            if name == "nope":
                cum, ac = True, None                                  # NOPE 本身就是"当天累计"的水平值
            else:
                ac = lag1_autocorr([r[key] for r in rows])
                cum = ac is not None and ac >= 0.9
            ms = MinSeries(rows, key, cum)
            pts[name].extend(signal_points(d, ser, lambda t, ms=ms: ms.window(t, SIG_WINDOW_MIN)))
            info[name].append((d, cum, ac, len(rows)))
    stats = {k: study_signal(v) for k, v in pts.items() if v}
    return {"stats": stats, "info": info}


# ---- 成交量价位 → POC / 价值区 ----
def parse_price_levels(raw, a_key: str, b_key: str):
    """成交量按价位的接口 → [(价位, a, b)]（升序）。a/b 的字段名：场内/场外 lit_vol/off_vol；暗池 dark_pool_volume/regular_volume；
    期权 call_volume/put_volume。"""
    out = []
    for r in _data_rows(raw):
        p = num(r.get("price"))
        if p is None or p <= 0:
            continue
        out.append((p, num(r.get(a_key)) or 0.0, num(r.get(b_key)) or 0.0))
    out.sort(key=lambda x: x[0])
    return out or None


def volume_profile(levels: list, bin_w=None, va_pct: float = 0.70):
    """levels = [(价位, 量, …)]（价位之后的数全部加总）。按 bin_w 美元分箱 → POC（量最大的箱的中心）和价值区
    （包住 va_pct 成交量的最小连续区间，标准的"两箱两箱"扩张法；VAH/VAL = 区间上沿/下沿）。无量返回 None。"""
    pts = [(x[0], sum(x[1:])) for x in levels if sum(x[1:]) > 0]
    if not pts:
        return None
    px = sorted(p for p, _ in pts)
    med = px[len(px) // 2]
    if bin_w is None:
        bin_w = max(0.05, round(med * 0.00035 / 0.05) * 0.05)      # SPY≈730 → $0.25
    bins: dict = {}
    for p, v in pts:
        k = int(math.floor(p / bin_w + 1e-9))
        bins[k] = bins.get(k, 0.0) + v
    k0, k1 = min(bins), max(bins)
    vols = [bins.get(k, 0.0) for k in range(k0, k1 + 1)]
    total = sum(vols)
    centers = [(k0 + i + 0.5) * bin_w for i in range(len(vols))]
    vwap = sum(c * v for c, v in zip(centers, vols)) / total
    top = max(vols)
    poc_i = min((i for i, v in enumerate(vols) if v == top), key=lambda i: abs(centers[i] - vwap))
    lo = hi = poc_i
    acc, n = vols[poc_i], len(vols)
    while acc < va_pct * total and (lo > 0 or hi < n - 1):
        up = (vols[hi + 1] + (vols[hi + 2] if hi + 2 < n else 0.0)) if hi + 1 < n else -1.0
        dn = (vols[lo - 1] + (vols[lo - 2] if lo - 2 >= 0 else 0.0)) if lo - 1 >= 0 else -1.0
        if up >= dn:
            acc += up
            hi = min(n - 1, hi + 2)
        else:
            acc += dn
            lo = max(0, lo - 2)
    return {"poc": centers[poc_i], "val": (k0 + lo) * bin_w, "vah": (k0 + hi + 1) * bin_w, "vwap": vwap,
            "total": total, "bin": bin_w, "n": len(pts)}


def touch_outcome(bars: list, level: float, tol_pct: float = 0.03, react_pct: float = 0.10, react_min: int = 20,
                  t_from=None, t_to=None):
    """价格第一次"碰到"level（进入 ±tol_pct 的带，且前一根收盘在带外，才知道是从哪边来的）之后 react_min 根分钟线内：
    先朝来的方向反弹 react_pct → "bounce"；先穿到另一边 react_pct → "break"；都没有（或同一根里两边都到）→ "none"；没碰到 → None。"""
    if not level or level <= 0:
        return None
    lo_z, hi_z = level * (1 - tol_pct / 100.0), level * (1 + tol_pct / 100.0)
    up_t, dn_t = level * (1 + react_pct / 100.0), level * (1 - react_pct / 100.0)
    prev_c = None
    for i, b in enumerate(bars):
        if t_from is not None and b["t"] < t_from:
            prev_c = b["c"]
            continue
        if t_to is not None and b["t"] > t_to:
            break
        if b["l"] <= hi_z and b["h"] >= lo_z and prev_c is not None and (prev_c > hi_z or prev_c < lo_z):
            side = 1 if prev_c > hi_z else -1                      # 1 = 从上方落下来（支撑测试），-1 = 从下方涨上来（压力测试）
            for b2 in bars[i + 1:i + 1 + react_min]:
                away = b2["h"] >= up_t if side > 0 else b2["l"] <= dn_t
                through = b2["l"] <= dn_t if side > 0 else b2["h"] >= up_t
                if away and through:
                    return "none"
                if away:
                    return "bounce"
                if through:
                    return "break"
            return "none"
        prev_c = b["c"]
    return None


SHIFTS = (-1.0, -0.75, -0.5, -0.35, 0.35, 0.5, 0.75, 1.0)        # 对照组：把真实价位整体平移这么多 %


def touch_study(day_levels: dict, bars_for, shifts=SHIFTS) -> dict:
    """day_levels = {交易日: [前一日算出的价位…]}；bars_for(日) → 当天分钟线。
    真实价位 vs 平移后的对照价位：价格第一次碰到之后，是"反弹"还是"穿过"。返回 {real/ctrl: {bounce, break, none, miss}}。"""
    cnt = {"real": {"bounce": 0, "break": 0, "none": 0, "miss": 0}, "ctrl": {"bounce": 0, "break": 0, "none": 0, "miss": 0}}
    for d in sorted(day_levels):
        bars = bars_for(d)
        if not bars:
            continue
        o_t, _c, _e = session_epochs(d)
        t_from, t_to = o_t + 15 * 60, o_t + 360 * 60                # 09:45 – 15:30
        for lv in day_levels[d]:
            cases = [("real", lv)] + [("ctrl", lv * (1 + s / 100.0)) for s in shifts]
            for kind, x in cases:
                out = touch_outcome(bars, x, t_from=t_from, t_to=t_to)
                cnt[kind]["miss" if out is None else out] += 1
    return cnt


def _bounce_rate(c: dict):
    n = c["bounce"] + c["break"]
    return (100.0 * c["bounce"] / n) if n else None


def fetch_stream_days(uw, label: str, call_fn, parse_fn, days: list, sleep, deadline: float, diag: list) -> dict:
    """逐日取一个"按日期"的接口，从最近的一天往回取，返回 {日: 解析后的行}。
    遇到 401/402/403（多半是超出历史范围）就不再往更早取；连续 2 次其它错误也停，免得白白浪费请求。"""
    out: dict = {}
    bad = 0
    for d in sorted(days, reverse=True):
        if time.monotonic() > deadline:
            diag.append(f"{label}：时间预算用完，只取到 {len(out)} 天")
            break
        r = call_fn(d)
        sleep(0.4)
        if not r.ok:
            diag.append(f"{label} {d:%m-%d} HTTP {r.status} {(r.err or '')[:80]}".strip())
            if r.status in (401, 402, 403):
                break
            bad += 1
            if bad >= 2:
                break
            continue
        bad = 0
        rows = parse_fn(r.data)
        if not rows:
            diag.append(f"{label} {d:%m-%d} 返回 0 行（结构：{shape(r.data)[:100]}）")
            continue
        out[d] = rows
    return out


def _dedupe_levels(levels: list, tol_pct: float = 0.05) -> list:
    out: list = []
    for x in levels:
        if x and all(abs(x - y) / y * 100.0 > tol_pct for y in out):
            out.append(x)
    return out


def study_levels(cfg: Cfg, uw, days: list, series_for, sleep, deadline: float, diag: list) -> dict:
    """前一日的成交量价位（POC / 价值区上下沿）能不能"挡住"今天的价格？
    对照：前一日的最高/最低/收盘价；以及把真实价位平移后的"假价位"（同样的算法，用来排除"任何一条横线都有这个反弹率"）。"""
    sym = cfg.symbol
    d_iso = lambda d: {"date": d.isoformat()}                       # noqa: E731
    srcs = (("暗池+常规", lambda d: uw.get(f"/api/darkpool/{sym}/price-levels", d_iso(d), retries=1),
             lambda raw: parse_price_levels(raw, "dark_pool_volume", "regular_volume")),
            ("场内+场外", lambda d: uw.get(f"/api/stock/{sym}/stock-volume-price-levels", d_iso(d), retries=1),
             lambda raw: parse_price_levels(raw, "lit_vol", "off_vol")))
    prof: dict = {}
    for name, call, parse in srcs:
        got = fetch_stream_days(uw, f"成交量价位·{name}", call, parse, days, sleep, deadline, diag)
        prof[name] = {d: p for d, p in ((d, volume_profile(rows)) for d, rows in got.items()) if p}
    prof = {k: v for k, v in prof.items() if v}
    if not prof:
        return {"err": "读不到成交量价位（见附录诊断）"}
    primary = max(prof, key=lambda k: sum(p["total"] for p in prof[k].values()))      # 总成交量更大的那个口径更完整
    pv = prof[primary]
    va_levels, hlc_levels = {}, {}
    ds = sorted(days)
    for prev, d in zip(ds, ds[1:]):
        if prev not in pv:
            continue
        p = pv[prev]
        va_levels[d] = _dedupe_levels([p["poc"], p["vah"], p["val"]])
        sp = series_for(prev)
        if sp is not None and sp.bars:
            hlc_levels[d] = _dedupe_levels([max(b["h"] for b in sp.bars), min(b["l"] for b in sp.bars), sp.bars[-1]["c"]])

    def bars_for(d):
        s = series_for(d)
        return s.bars if s is not None else None

    va = touch_study({d: v for d, v in va_levels.items() if bars_for(d)}, bars_for)
    hlc = touch_study({d: v for d, v in hlc_levels.items() if bars_for(d)}, bars_for)
    last_d = max(pv)
    return {"primary": primary, "profiles": prof, "last": (last_d, pv[last_d]), "va": va, "hlc": hlc,
            "n_days": len(va_levels)}


def levels_verdict(res: dict) -> tuple:
    if res.get("err"):
        return CHIP_ERR, res["err"]
    va = res["va"]
    n_real = va["real"]["bounce"] + va["real"]["break"]
    r_real, r_ctrl = _bounce_rate(va["real"]), _bounce_rate(va["ctrl"])
    if res["n_days"] < MIN_STUDY_DAYS or n_real < 40 or r_ctrl is None:       # 少于 40 次有效触碰：差 15 个点也在误差范围内，不下结论
        return CHIP_THIN, f"只测到 {n_real} 次有效触碰（{res['n_days']} 天），样本不足，只当参考"
    gap = r_real - r_ctrl
    if abs(gap) >= 15:
        way = "" if gap > 0 else "（反过来：这些线更容易被穿过）"
        return CHIP_OK, f"有线索：价格碰到前一日价值区的线后，反弹率 {r_real:.0f}% vs 对照 {r_ctrl:.0f}%{way}（需更多天确认）"
    return CHIP_FLAT, f"反弹率 {r_real:.0f}% 与对照 {r_ctrl:.0f}% 差不多，没看出这些线比随便一条线更挡价"


# ---- 各部分的"要点"与"附录"----
def _sec(key: str, title: str) -> dict:
    return {"key": key, "title": title, "chip": CHIP_NA, "head": "", "lines": [], "app": []}


def section_alerts(cfg: Cfg, results: list, days: list, app_lines: list) -> dict:
    sec = _sec("alerts", "提醒入场")
    sec["app"] = app_lines
    if not results:
        sec["head"] = "没有可回测的提醒（journal 里还没有记录）"
        return sec
    n = len(results)
    spot = [r["spot"] for r in results if r.get("spot")]
    opt = [r["opt"] for r in results if r.get("opt")]
    kinds = "｜".join(f"{KIND_ICON[k]}{KIND_NAME[k]}{sum(1 for r in results if r['a']['k'] == k)}"
                      for k in ("conf", "single", "mega") if any(r["a"]["k"] == k for r in results))
    span = f"{days[0]:%m-%d}" + (f"～{days[-1]:%m-%d}" if len(days) > 1 else " 一天")
    sec["lines"].append(f"{n} 条提醒（{kinds}）｜{span}")
    delay = f"（再延后 {cfg.bt_delay_min:g} 分钟）" if cfg.bt_delay_min else ""
    sec["lines"].append(f"入场 = 提醒后下一分钟开盘价{delay}；现货 = 按提醒方向做多/做空 SPY；"
                        f"期权 = 同方向最近平值 0DTE，买卖各扣 ${cfg.bt_slip:.2f}/股点差")

    def seg(tracks, fmt):
        out = []
        for h in (15, 60):
            k, w, m, md = _agg([t["ret"].get(h) for t in tracks])
            out.append(f"+{h}m 赢{w}/{k} 均{fmt(m)} 中位{fmt(md)}" if k else f"+{h}m 无数据")
        return "｜".join(out)

    sec["lines"].append("现货 SPY：" + seg(spot, _pc))
    sec["lines"].append("期权 0DTE：" + seg(opt, _po))
    mf = [t["mfe"] for t in opt if t.get("mfe") is not None]
    ma = [t["mae"] for t in opt if t.get("mae") is not None]
    if mf and ma:
        sec["lines"].append(f"入场后 60 分钟内（期权，均值）：最好 {_po(sum(mf) / len(mf))}｜最差 {_po(sum(ma) / len(ma))}")
    by_kind = []
    for k in ("conf", "single", "mega"):
        sub = [r for r in results if r["a"]["k"] == k]
        if sub:
            sp = _agg([(r.get("spot") or {}).get("ret", {}).get(60) for r in sub])
            op = _agg([(r.get("opt") or {}).get("ret", {}).get(60) for r in sub])
            by_kind.append(f"{KIND_ICON[k]}{KIND_NAME[k]}{len(sub)}条 现货{_pc(sp[2])} 期权中位{_po(op[3])}")
    if by_kind:
        sec["lines"].append("按类型（+60m）：" + "｜".join(by_kind))
    o60, s60 = _agg([t["ret"].get(60) for t in opt]), _agg([t["ret"].get(60) for t in spot])
    skew = bool(o60[0]) and o60[2] is not None and o60[3] is not None and o60[2] > 0 > o60[3]
    if len(days) < MIN_STUDY_DAYS or n < 30:
        sec["chip"], sec["head"] = CHIP_THIN, f"只有 {len(days)} 天、{n} 条提醒，样本太少，下不了结论"
    elif o60[0] and o60[3] is not None and o60[3] > 0 and o60[1] / o60[0] >= 0.55 and s60[2] is not None and s60[2] > 0:
        sec["chip"], sec["head"] = CHIP_OK, f"有线索：期权 +60m 中位 {_po(o60[3])}、{o60[1]}/{o60[0]} 赢，现货均 {_pc(s60[2])}（需更多天确认）"
    else:
        sec["chip"], sec["head"] = CHIP_FLAT, f"期权 +60m 中位 {_po(o60[3])}、现货均 {_pc(s60[2])}，看不出优势"
    if skew:
        sec["head"] += "；期权的平均数被少数大赢家拉高（中位数为负）"
    return sec


def flow_edge(rows: list, bull: tuple, bear: tuple, H: int) -> dict:
    """偏多标签之后的 SPY 平均涨跌 − 偏空标签之后的（%）。两组同时受大盘涨跌影响，相减后基本抵消。"""
    def mean(cats):
        v = [r["r"].get(H) for r in rows if r["cat"] in cats and r["r"].get(H) is not None]
        return (sum(v) / len(v), len(v)) if v else (None, 0)

    a, na = mean(bull)
    b, nb = mean(bear)
    return {"edge": (a - b) if a is not None and b is not None else None, "na": na, "nb": nb}


def flow_edge_by_day(rows: list, bull: tuple, bear: tuple, H: int, min_side: int = 5):
    pos = n = 0
    for d in sorted({r["day"] for r in rows}):
        e = flow_edge([r for r in rows if r["day"] == d], bull, bear, H)
        if e["edge"] is not None and e["na"] >= min_side and e["nb"] >= min_side:
            n += 1
            pos += 1 if e["edge"] > 0 else 0
    return pos, n


def section_flow(cfg: Cfg, rows: list, days: list, n_items: int, app_lines: list) -> dict:
    sec = _sec("flow", "大单买卖标签")
    sec["app"] = app_lines
    if not rows:
        sec["chip"], sec["head"] = CHIP_THIN, "没有取到足够的大单样本（见附录诊断）"
        return sec
    sec["lines"].append(f"≥{money(cfg.print_min)} 的大单 {n_items} 条（可用 {len(rows)} 条）｜{len(days)} 天")
    sec["lines"].append("问：偏多标签（买Call/卖Put）之后，SPY 是不是比偏空标签（买Put/卖Call）之后涨得多？看\"多空差\"：")
    pos, nd = flow_edge_by_day(rows, BULL_CATS, BEAR_CATS, 15)
    groups = (("全部标签", BULL_CATS, BEAR_CATS), ("买入型 买Call−买Put", ("buy_call",), ("buy_put",)),
              ("卖出型 卖Put−卖Call", ("sell_put",), ("sell_call",)))
    res = {}
    for name, bull, bear in groups:
        e15, e60 = flow_edge(rows, bull, bear, 15), flow_edge(rows, bull, bear, 60)
        res[name] = (e15, e60)
        extra = f"｜按天 {pos}/{nd} 为正" if name == "全部标签" and nd else ""
        sec["lines"].append(f" {name}：15m {_pc(e15['edge'])}｜60m {_pc(e60['edge'])}（n {e15['na']}／{e15['nb']}）{extra}")
    dte_parts = []
    for label, bks in (("0DTE", ("0DTE",)), ("1–5天", ("1–5天",)), ("6天以上", ("6–30天", "30天+"))):
        sub = [r for r in rows if dte_bucket(r["dte"]) in bks]
        e = flow_edge(sub, BULL_CATS, BEAR_CATS, 15)
        ok = e["edge"] is not None and min(e["na"], e["nb"]) >= 30
        dte_parts.append(f"{label} {_pc(e['edge']) if ok else '样本少'}（n {e['na']}／{e['nb']}）")
    sec["lines"].append(" 按到期（全部标签 15m）：" + "｜".join(dte_parts))
    tot = len(rows)
    share = {b: sum(1 for r in rows if dte_bucket(r["dte"]) in bks) for b, bks in
             (("0DTE", ("0DTE",)), ("1–5天", ("1–5天",)), ("6天以上", ("6–30天", "30天+")))}
    zero_p = sum(r["prem"] or 0 for r in rows if dte_bucket(r["dte"]) == "0DTE")
    all_p = sum(r["prem"] or 0 for r in rows)
    zp = 100.0 * zero_p / all_p if all_p else 0.0
    note = "——你做的是 0DTE，这些大单大多是更远期的，参考价值有限" if 100.0 * share["0DTE"] / tot < 30 else ""
    sec["lines"].append(" 到期分布（按条数）：" + "｜".join(f"{b} {100.0 * n / tot:.0f}%" for b, n in share.items())
                        + f"｜0DTE 按金额 {zp:.0f}%{note}")
    e15, e60 = res["全部标签"]
    nmin = min(e15["na"], e15["nb"])
    if len(days) < MIN_STUDY_DAYS or nmin < MIN_SIDE_N or e15["edge"] is None:
        sec["chip"], sec["head"] = CHIP_THIN, f"样本不足（{len(days)} 天，偏多/偏空各 {e15['na']}／{e15['nb']} 条）"
    else:
        x15, x60 = e15["edge"], e60["edge"]
        cons = _consistent(pos, nd, x15 > 0)
        if abs(x15) >= EDGE_MIN_PCT and x60 is not None and x15 * x60 > 0 and cons:
            way = "有线索" if x15 > 0 else "标签方向反着走（偏多之后反而涨得少）"
            sec["chip"], sec["head"] = CHIP_OK, f"{way}：多空差 15m {_pc(x15)}｜60m {_pc(x60)}，按天 {pos}/{nd} 一致（需更多天确认）"
        else:
            if abs(x15) < EDGE_MIN_PCT:
                why = f"幅度不到 {EDGE_MIN_PCT:.2f}%，盖不住期权点差——买卖标签没有可用的方向信息"
            elif x60 is None or x15 * x60 <= 0:
                why = "15m 与 60m 方向不一致，不下结论"
            else:
                why = f"按天只有 {pos}/{nd} 一致，不稳定，不下结论"
            sec["chip"], sec["head"] = CHIP_FLAT, f"多空差 15m {_pc(x15)}｜60m {_pc(x60)}，{why}"
    return sec


def section_signals(res: dict) -> dict:
    sec = _sec("signals", "Greek flow / NOPE")
    stats, info = res.get("stats") or {}, res.get("info") or {}
    chip, head = signals_verdict(stats)
    sec["chip"], sec["head"] = chip, head
    if not stats:
        return sec
    nd = max(s["days"] for s in stats.values())
    npt = max(s["n"] for s in stats.values())
    sec["lines"].append(f"{nd} 天｜每 {SIG_STEP_MIN} 分钟看一次（共 {npt} 个观察点）｜信号 = 近 {SIG_WINDOW_MIN} 分钟的方向性 delta 流"
                        "（NOPE = 近 15 分钟的变化）")
    sec["lines"].append("问：信号强的时候，之后的 SPY 是不是真的涨/跌得更多？（相关 > 0 = 流向偏多之后涨；"
                        "强1/3−弱1/3 = 信号最强的三分之一时点之后的平均涨跌，减信号最弱的三分之一）")
    for name in ("gf_all", "gf_0dte", "nope"):
        s = stats.get(name)
        if not s:
            sec["lines"].append(f" {SIG_NAMES[name]}：没有数据")
            continue
        h15, h60 = s["h"][15], s["h"][60]
        ts = h15["ts"]
        tail = f"｜强1/3−弱1/3 15m {_pc(ts['spread'])}（按天 {ts['day_pos']}/{ts['day_n']} 为正）" if ts else ""
        sec["lines"].append(f" {SIG_NAMES[name]}：之后15m 相关 {_cc(h15['corr'])}｜之后60m {_cc(h60['corr'])}{tail}")
    sec["lines"].append(" 对照——与\"之前 15 分钟\"涨跌的相关："
                        + "｜".join(f"{SIG_NAMES[k]} {_cc(stats[k]['past'])}" for k in ("gf_all", "gf_0dte", "nope") if k in stats))
    noise = max(h["noise"] for s in stats.values() for h in s["h"].values())
    sec["lines"].append(f" 噪声范围：相关系数在 ±{noise:.2f} 以内，可能只是运气（样本重叠，有效样本远少于点数）")
    # 附录：全部周期 + 数据口径判定
    app = ["🌊 附录C｜Greek flow / NOPE 全部结果（相关 = 秩相关；强1/3−弱1/3 = 信号最强的三分之一减最弱的三分之一，之后 SPY 平均涨跌之差）"]
    for name in ("gf_all", "gf_0dte", "nope"):
        s = stats.get(name)
        if not s:
            continue
        app.append(f"  {SIG_NAMES[name]}｜{s['days']} 天 {s['n']} 点｜与之前15m涨跌相关 {_cc(s['past'])}")
        for H in (5, 15, 30, 60):
            h = s["h"][H]
            ts = h["ts"]
            tail = f"｜强1/3−弱1/3 {_pc(ts['spread'])}（n {ts['n_hi']}／{ts['n_lo']}｜按天 {ts['day_pos']}/{ts['day_n']}）" if ts else "｜强弱差 —"
            app.append(f"    之后{H}m：相关 {_cc(h['corr'])}（噪声±{h['noise']:.2f}｜n={h['n']}）{tail}")
    for name in ("gf_all", "gf_0dte", "nope"):
        rows = info.get(name) or []
        if rows:
            n_cum = sum(1 for _d, c, _a, _n in rows if c)
            acs = [a for _d, _c, a, _n in rows if a is not None]
            how = "当天累计值（已做差）" if n_cum * 2 > len(rows) else "逐分钟增量（已求和）"
            ac_t = f"｜lag1 自相关 {sum(acs) / len(acs):.2f}" if acs else ""
            app.append(f"  口径判定·{SIG_NAMES[name]}：{how}{ac_t}｜{len(rows)} 天")
    sec["app"] = app
    return sec


def section_levels(res: dict) -> dict:
    sec = _sec("levels", "前一日价值区（POC）")
    chip, head = levels_verdict(res)
    sec["chip"], sec["head"] = chip, head
    if res.get("err"):
        return sec
    d, p = res["last"]
    sec["lines"].append(f"最新一日 {d:%m-%d}（{res['primary']}口径）：POC {p['poc']:.2f}｜价值区 {p['val']:.2f}–{p['vah']:.2f}｜成交量加权均价 {p['vwap']:.2f}")
    others = [f"{k} POC {v[d]['poc']:.2f}" for k, v in res["profiles"].items() if k != res["primary"] and d in v]
    if others:
        sec["lines"].append("  对照其它口径：" + "｜".join(others))

    def row(name, c):
        r = _bounce_rate(c)
        return f"{name}：反弹 {c['bounce']}｜穿过 {c['break']}｜无反应 {c['none']}（反弹率 {f'{r:.0f}%' if r is not None else '—'}）"

    sec["lines"].append(f"挡价测试（{res['n_days']} 天）：价格第一次碰到某条线后 20 分钟内，先反弹 0.10% 还是先穿过 0.10%")
    sec["lines"].append(" " + row("前一日 POC＋价值区上下沿", res["va"]["real"]))
    sec["lines"].append(" " + row("对照：把这三条线平移后的假价位", res["va"]["ctrl"]))
    sec["lines"].append(" " + row("参考：前一日 最高/最低/收盘", res["hlc"]["real"]))
    miss = f"  没碰到价位的次数：真实价位 {res['va']['real']['miss']}｜对照 {res['va']['ctrl']['miss']}｜前一日高低收 {res['hlc']['real']['miss']}"
    sec["app"] = ["📦 附录D｜成交量价位口径与明细", miss] + [
        f"  {k}：{len(v)} 天｜最新 {max(v):%m-%d} POC {v[max(v)]['poc']:.2f} 价值区 {v[max(v)]['val']:.2f}–{v[max(v)]['vah']:.2f}｜分箱 ${v[max(v)]['bin']:.2f}"
        f"｜总量 {v[max(v)]['total'] / 1e6:.1f}M"
        for k, v in res["profiles"].items()] + [
        "  规则：POC = 成交量最大的价位箱；价值区 = 包住 70% 成交量的最小连续区间；碰到 = 价格进入线 ±0.03% 且前一根收盘在带外；",
        "  对照价位 = 真实价位整体平移 ±0.35/0.5/0.75/1.0%，用同样的方法测，用来排除\"任何横线都有这个反弹率\"。"]
    return sec


def section_gamma() -> dict:
    sec = _sec("gamma", "0DTE 按行权价 gamma")
    sec["head"] = "历史接口只给当天最后一个快照，回测会带入未来信息，本次不测"
    sec["lines"] = ["按文档，查历史日期只返回该日\"最近的一个快照\"（收盘附近）；拿它去\"预测\"盘中价格，等于偷看答案。",
                    "办法：让监控从现在起每 5 分钟记一次 0DTE 快照，攒 2–3 周后再测\"哪些行权价真的挡得住价格\"。接口的实际返回样子，可以用 probe 模式看。"]
    return sec


def build_research_report(cfg: Cfg, secs: list, span: tuple, ndays: int, diag: list) -> tuple:
    """→ (结论页, 要点页, 附录) 三组行。结论页必须能在一条消息里发完。"""
    L1 = [f"📌 SPY 研究报告｜{span[0]:%Y-%m-%d}～{span[1]:%m-%d}（{ndays} 个交易日）", "【先看结论】"]
    for s in secs:
        L1.append(f"{s['chip']} {s['title']}：{s['head']}")
    cnt = {c: sum(1 for s in secs if s["chip"] == c) for c in (CHIP_OK, CHIP_FLAT, CHIP_THIN, CHIP_NA, CHIP_ERR)}
    if cnt[CHIP_OK]:
        L1.append(f"→ 有 {cnt[CHIP_OK]} 项出现线索（🟢），但都还要更多天确认；其余没有证据。")
    elif cnt[CHIP_FLAT]:
        L1.append("→ 样本够的部分（⚪）都没看出优势；其余样本不够或没读到数据，暂时没有结论。")
    else:
        L1.append("→ 这次样本不够或没读到数据，暂时没有结论：既不能说有用，也不能说没用。")
    L1 += ["【怎么读】",
           "🟢 有线索（仍需更多天确认）｜⚪ 样本够、但看不出优势｜🟡 样本不够，不下结论｜➖ 本次没测｜⚠ 读不到数据",
           f"「多空差」= 偏多标签之后 SPY 的平均涨跌 − 偏空标签之后的（基本不受当天趋势影响）；±{EDGE_MIN_PCT:.2f}% 以内，盖不住 0DTE 期权的点差和时间损耗。",
           "【下一步】"]
    steps = []
    if ndays < 10:
        steps.append("想要更可靠的结论：仓库 Settings → Secrets and variables → Actions → Variables 里新建 BT_FLOW_DAYS = 20，再运行一次 backtest（样本约放大 4 倍）。")
    if any(s["key"] == "gamma" and s["chip"] == CHIP_NA for s in secs):
        steps.append("0DTE 按行权价 gamma 需要先积累快照：可以让监控从明天起自动记录（要改一次代码；不影响现有提醒）。")
    steps.append("本报告只检验\"信号有没有预测力\"，面板和提醒的逻辑一律没改。")
    L1.extend(f"• {x}" for x in steps)

    L2 = []
    for s in secs:
        if not s["lines"]:
            continue
        L2.append(f"{s['chip']} {s['title']}")
        L2.extend(s["lines"])
        L2.append("")
    if L2 and L2[-1] == "":
        L2.pop()

    L3 = ["📎 附录（需要细看时再翻；以上结论不依赖这些）"]
    for s in secs:
        if s["app"]:
            L3.extend(s["app"])
    if diag:
        L3.append("【数据诊断】")
        L3.extend(f"  {x}" for x in diag)
    return L1, L2, (L3 if len(L3) > 1 else [])


def send_lines(tg, lines: list, limit: int = 3500, silent: bool = False) -> list:
    msgs, cur = [], ""
    for ln in lines:
        if cur and len(cur) + len(ln) + 1 > limit:
            msgs.append(cur)
            cur = ""
        cur += ("\n" if cur else "") + ln
    if cur:
        msgs.append(cur)
    for m in msgs:
        if tg.send(m, silent=silent) is None:
            log("Telegram 发送失败：", tg.last_error)
    return msgs


def recent_trading_days(now: datetime, n: int) -> list:
    """最近 n 个已收盘（或今天 16:10 之后）的工作日，升序。节假日会因取不到数据而被自动跳过。"""
    t = now.astimezone(ET)
    d, out = t.date(), []
    if t.weekday() >= 5 or t.time() < dtime(16, 10):
        d -= timedelta(days=1)
    while len(out) < n:
        if d.weekday() < 5:
            out.append(d)
        d -= timedelta(days=1)
    return sorted(out)


def run_backtest(cfg: Cfg, uw, tg, sleep=time.sleep, state_path: str = STATE_FILE, now_fn=now_et) -> None:
    """研究报告：① 提醒入场回测 ② 大单买卖标签 ③ Greek flow / NOPE ④ 前一日价值区 ⑤ 0DTE 行权价 gamma（只说明为什么不测）。
    每一部分单独 try，一部分出错不影响其它；最后依次发：结论页 → 要点页 → 附录。"""
    now = now_fn()
    series_cache: dict = {}
    spy_raw: dict = {}

    def series_for(day):
        if day not in series_cache:
            bars, dg = fetch_spy_bars(uw, cfg, day, sleep)
            series_cache[day] = BarSeries(bars) if len(bars) >= 100 else None
            spy_raw[day] = dg
        return series_cache[day]

    def spy_diag_lines(days_used) -> list:
        normal, out = [], []
        for d in days_used:
            dg = spy_raw.get(d)
            if dg is None:
                continue
            m = re.search(r"(\d+)根$", dg[0]) if len(dg) == 1 else None
            if m and int(m.group(1)) >= 380:
                normal.append(d)
            else:
                out.append(f"{d:%m-%d} SPY 1分钟线：" + "｜".join(dg))
        if normal:
            out.insert(0, f"SPY 1分钟线：{len(normal)} 天正常（{'、'.join(f'{d:%m-%d}' for d in normal[:3])}{'…' if len(normal) > 3 else ''}）")
        return out

    def err_sec(key, title, e):
        s = _sec(key, title)
        s["chip"], s["head"] = CHIP_ERR, f"这一部分出错：{type(e).__name__}（其它部分不受影响）"
        return s

    tg.send("⏳ 研究报告开始生成（约 3–8 分钟）。完成后依次发：结论 → 要点 → 附录。", silent=True)
    secs: list = []
    diag: list = []
    alert_days: list = []

    # ① 提醒回测：journal + 内置样本
    try:
        alerts = collect_alerts(cfg, state_path)
        if alerts:
            results, alert_days = run_alert_backtest(cfg, uw, alerts, series_for, sleep)
            diag += spy_diag_lines(alert_days)
            diag += [r["opt_err"] for r in results if r.get("opt_err") and "无法入场" not in r["opt_err"]][:6]
            secs.append(section_alerts(cfg, results, alert_days, build_backtest_report(cfg, results, alert_days)))
        else:
            s = _sec("alerts", "提醒入场")
            s["head"] = "没有可回测的提醒（journal 里还没有记录，且内置样本已关闭）"
            secs.append(s)
    except Exception as e:  # noqa: BLE001
        log("提醒回测出错：", type(e).__name__, e)
        secs.append(err_sec("alerts", "提醒入场", e))

    fdays: list = []
    if cfg.bt_flow_days > 0:
        all_days = recent_trading_days(now, cfg.bt_flow_days + 1)       # 多取最早一天：只用来算"前一日"的价值区
        fdays = all_days[1:]
        # ② 大单买卖标签：最近几个交易日的 UW flow-alerts × SPY 分钟线
        try:
            t_start = datetime(fdays[0].year, fdays[0].month, fdays[0].day, 9, 25, tzinfo=ET).timestamp()
            t_end = min(datetime(fdays[-1].year, fdays[-1].month, fdays[-1].day, 16, 20, tzinfo=ET).timestamp(), now.timestamp())
            items, fdiag = fetch_flow_history(uw, cfg, t_start, t_end, sleep)
            diag.append("flow-alerts：" + "｜".join(x.replace("flow-alerts ", "") for x in fdiag))
            if not items:
                s = _sec("flow", "大单买卖标签")
                s["chip"], s["head"] = CHIP_ERR, "没有取到大单记录（见附录诊断）"
                secs.append(s)
            else:
                rows = flow_study_rows(items, series_for)
                sdays = sorted({r["day"] for r in rows})
                diag += spy_diag_lines(sdays)
                if len(rows) < 20:
                    s = _sec("flow", "大单买卖标签")
                    s["chip"], s["head"] = CHIP_THIN, f"取到 {len(items)} 条大单，但能配上 SPY 分钟线的只有 {len(rows)} 条，样本不足"
                    secs.append(s)
                else:
                    secs.append(section_flow(cfg, rows, sdays, len(items), build_flow_study_report(cfg, rows, sdays, len(items))))
        except Exception as e:  # noqa: BLE001
            log("大单分类回测出错：", type(e).__name__, e)
            secs.append(err_sec("flow", "大单买卖标签", e))

        # ③④⑤ 新数据流：Greek flow / NOPE、前一日价值区、0DTE 行权价 gamma
        deadline = time.monotonic() + cfg.bt_stream_s
        sdiag: list = []
        try:
            secs.append(section_signals(study_flow_signals(cfg, uw, fdays, series_for, sleep, deadline, sdiag)))
        except Exception as e:  # noqa: BLE001
            log("Greek flow / NOPE 检验出错：", type(e).__name__, e)
            secs.append(err_sec("signals", "Greek flow / NOPE", e))
        try:
            secs.append(section_levels(study_levels(cfg, uw, all_days, series_for, sleep, deadline, sdiag)))
        except Exception as e:  # noqa: BLE001
            log("成交量价位检验出错：", type(e).__name__, e)
            secs.append(err_sec("levels", "前一日价值区（POC）", e))
        secs.append(section_gamma())
        diag += sdiag
        diag += [x for x in spy_diag_lines(all_days) if x not in diag]

    ok_days = [d for d in fdays if series_cache.get(d) is not None] or fdays or alert_days or [now.astimezone(ET).date()]
    ok_days = sorted(ok_days)
    try:
        L1, L2, L3 = build_research_report(cfg, secs, (ok_days[0], ok_days[-1]), len(ok_days), diag)
    except Exception as e:  # noqa: BLE001
        log("研究报告排版出错：", type(e).__name__, e)
        tg.send(f"⚠ 研究报告排版出错：{type(e).__name__}（各部分已算完，但没能整理成报告；详情见 Actions 日志）", silent=False)
        raise
    send_lines(tg, L1)                       # 只有结论页响铃；要点页和附录静音，免得连响三次
    if L2:
        send_lines(tg, L2, silent=True)
    if L3:
        send_lines(tg, L3, silent=True)


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
    if cfg.mode == "backtest":
        run_backtest(cfg, uw, tg)
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
