"""
FlashAlpha 关键点位/结构性指标/动量监控 -> Telegram 推送

监控内容：
1. 价格穿越 Gamma Flip（带缓冲带，避免贴线抖动误报）/ Call Wall / Put Wall
2. Dealer Gamma Regime 翻转
3. 价格突破当日 Expected Move 上下沿
4. 【破位延续确认-结构性信号】结构性破位后，只要价格没有反转回破位价，就持续追踪
   （不设固定时间上限），一旦沿破位方向累计走出 CONTINUATION_THRESHOLD_PCT% 就提醒；
   如果价格反转回破位价，视为该次破位论"证伪"，停止追踪。专门标注"这段走势紧跟哪次结构性破位"。
5. 【价格里程碑-通用兜底】不依赖任何破位/穿越事件，维护一个参考点(pivot)，
   价格从参考点每走出 MOMENTUM_THRESHOLD_PCT% 就提醒一次并重置参考点，不设时间上限。
   覆盖条件4覆盖不到的场景：已经在某一侧持续涨跌、或触发过一次后继续延伸的后续里程碑。

防噪音机制：
- Gamma Flip 穿越使用滞后判断（GAMMA_FLIP_BUFFER），贴线小幅抖动不算新穿越
- 所有触发类型都有全局冷却时间（COOLDOWN_MINUTES），同类型短时间内不会重复刷屏
"""

import json
import os
import sys
import time
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo

import requests

SYMBOL = os.environ.get("SYMBOL", "SPY")
FLASHALPHA_API_KEY = os.environ["FLASHALPHA_API_KEY"]
TELEGRAM_BOT_TOKEN = os.environ["TELEGRAM_BOT_TOKEN"]
TELEGRAM_CHAT_ID = os.environ["TELEGRAM_CHAT_ID"]

MOMENTUM_THRESHOLD_PCT = float(os.environ.get("MOMENTUM_THRESHOLD_PCT", "0.2"))
CONTINUATION_THRESHOLD_PCT = float(os.environ.get("CONTINUATION_THRESHOLD_PCT", "0.2"))
GAMMA_FLIP_BUFFER = float(os.environ.get("GAMMA_FLIP_BUFFER", "0.15"))
COOLDOWN_MINUTES = float(os.environ.get("COOLDOWN_MINUTES", "15"))

STATE_FILE = "state.json"
LEVELS_URL = f"https://lab.flashalpha.com/v1/exposure/levels/{SYMBOL}"
MAXPAIN_URL = f"https://lab.flashalpha.com/v1/maxpain/{SYMBOL}"
TELEGRAM_URL = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"

REGIME_LABEL = {
    "negative_gamma": "Negative Gamma（做市商顺势对冲，趋势相对容易延续）",
    "positive_gamma": "Positive Gamma（做市商逆势对冲，大范围内波动相对容易被压制）",
}


def in_market_hours() -> bool:
    if os.environ.get("FORCE_RUN", "").lower() == "true":
        return True
    now = datetime.now(ZoneInfo("America/New_York"))
    if now.weekday() >= 5:
        return False
    start = now.replace(hour=9, minute=30, second=0, microsecond=0)
    end = now.replace(hour=15, minute=45, second=0, microsecond=0)
    return start <= now <= end


def seconds_until_window_close() -> float:
    if os.environ.get("FORCE_RUN", "").lower() == "true":
        return 3600.0
    now = datetime.now(ZoneInfo("America/New_York"))
    end = now.replace(hour=15, minute=45, second=0, microsecond=0)
    return (end - now).total_seconds()


def now_et() -> datetime:
    return datetime.now(ZoneInfo("America/New_York"))


def today_et_str() -> str:
    return now_et().strftime("%Y-%m-%d")


def now_et_str() -> str:
    return now_et().strftime("%H:%M ET")


def load_state() -> dict:
    if os.path.exists(STATE_FILE):
        with open(STATE_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    return {}


def save_state(state: dict) -> None:
    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False, indent=2)


def send_telegram(text: str) -> None:
    resp = requests.post(TELEGRAM_URL, json={"chat_id": TELEGRAM_CHAT_ID, "text": text}, timeout=15)
    resp.raise_for_status()


def side_simple(price: float, level: float) -> str:
    return "above" if price >= level else "below"


def side_with_hysteresis(price: float, level: float, buffer: float, prev_side):
    """滞后判断：贴线在缓冲带内小幅抖动不算换边，必须真正超出缓冲带才算新的一侧。"""
    if prev_side is None:
        return side_simple(price, level)
    if prev_side == "above":
        return "below" if price < level - buffer else "above"
    return "above" if price > level + buffer else "below"


def fetch(url: str) -> dict:
    resp = requests.get(url, headers={"X-Api-Key": FLASHALPHA_API_KEY}, timeout=15)
    resp.raise_for_status()
    return resp.json()


def oi_at_strike(mp_data: dict, strike: float):
    for row in mp_data.get("oi_by_strike", []):
        if row.get("strike") == strike:
            return row
    return None


def is_top_oi_strike(mp_data: dict, strike: float, top_n: int = 5) -> bool:
    rows = mp_data.get("oi_by_strike", [])
    if not rows:
        return False
    sorted_rows = sorted(rows, key=lambda r: r.get("total_oi", 0), reverse=True)
    return strike in {r["strike"] for r in sorted_rows[:top_n]}


def pct_change(new: float, old: float) -> float:
    return (new - old) / old * 100 if old else 0.0


def cooldown_ok(last_fired: dict, key: str, now: datetime) -> bool:
    last = last_fired.get(key)
    if not last:
        return True
    return (now - datetime.fromisoformat(last)).total_seconds() / 60 >= COOLDOWN_MINUTES


def check_once() -> None:
    now = now_et()
    levels_data = fetch(LEVELS_URL)
    price = levels_data["underlying_price"]
    levels = levels_data["levels"]

    try:
        mp_data = fetch(MAXPAIN_URL)
    except Exception:
        mp_data = {}
    regime = mp_data.get("regime")
    expected_move = mp_data.get("expected_move", {})
    straddle_price = expected_move.get("straddle_price")
    atm_iv = expected_move.get("atm_iv")

    all_state = load_state()
    prev_state = all_state.get(SYMBOL, {})
    today = today_et_str()
    same_day = prev_state.get("date") == today
    new_state = {"underlying_price": price, "as_of": levels_data.get("as_of"), "date": today}
    last_fired = dict(prev_state.get("last_fired", {})) if same_day else {}
    candidates = []  # (message, trigger_type, cooldown_key)

    # ============ 条件 1：三条线穿越（Gamma Flip 带缓冲带滞后判断）============
    gf_value = levels.get("gamma_flip")
    prev_gf_side = prev_state.get("gamma_flip") if same_day else None
    gf_side = side_with_hysteresis(price, gf_value, GAMMA_FLIP_BUFFER, prev_gf_side) if gf_value else None
    new_state["gamma_flip"] = gf_side
    new_state["gamma_flip_value"] = gf_value

    new_breaks = []
    if prev_gf_side is not None and gf_value is not None and prev_gf_side != gf_side:
        direction = "向上突破" if gf_side == "above" else "向下跌破"
        candidates.append((
            f"Gamma Flip {direction} {gf_value:.2f}（当前价 {price:.2f}，缓冲带 ±{GAMMA_FLIP_BUFFER}）",
            "level_cross", "gamma_flip"
        ))
        new_breaks.append({"level": "Gamma Flip", "direction": "up" if gf_side == "above" else "down",
                            "break_price": price, "fired": False})

    for label, state_key, level_key in [("Call Wall", "call_wall", "call_wall"), ("Put Wall", "put_wall", "put_wall")]:
        level_value = levels.get(level_key)
        if level_value is None:
            continue
        current_side = side_simple(price, level_value)
        new_state[state_key] = current_side
        new_state[f"{state_key}_value"] = level_value
        prev_side = prev_state.get(state_key) if same_day else None
        if prev_side is not None and prev_side != current_side:
            direction = "向上突破" if current_side == "above" else "向下跌破"
            overshoot = abs(price - level_value)
            msg = f"{label} {direction} {level_value:.2f}（当前价 {price:.2f}，超出 {overshoot:.2f}）"
            oi_row = oi_at_strike(mp_data, level_value)
            if oi_row:
                rank_note = "（当前到期日 OI 最集中的行权价之一，对冲压力较大）" if is_top_oi_strike(mp_data, level_value) else "（OI 不算最集中，对冲压力相对有限）"
                msg += f"\n  该行权价持仓：Call {oi_row['call_oi']:,} / Put {oi_row['put_oi']:,} {rank_note}"
            candidates.append((msg, "level_cross", state_key))
            new_breaks.append({"level": label, "direction": "up" if current_side == "above" else "down",
                                "break_price": price, "fired": False})

    # ============ 条件 2：Regime 翻转 ============
    new_state["regime"] = regime
    prev_regime = prev_state.get("regime") if same_day else None
    if regime and prev_regime and regime != prev_regime:
        dist_note = f"，现价距 Gamma Flip {price - gf_value:+.2f}" if gf_value else ""
        candidates.append((f"Gamma Regime 翻转：{prev_regime} → {regime}{dist_note}", "regime", "regime"))

    # ============ 条件 3：Expected Move 上下沿突破 ============
    if same_day and "em_upper" in prev_state:
        em_upper, em_lower, em_anchor = prev_state["em_upper"], prev_state["em_lower"], prev_state["em_anchor"]
    elif straddle_price is not None:
        em_anchor, em_upper, em_lower = price, price + straddle_price, price - straddle_price
    else:
        em_anchor = em_upper = em_lower = None

    if em_upper is not None:
        new_state.update(em_anchor=em_anchor, em_upper=em_upper, em_lower=em_lower)
        current_em_side = "above" if price > em_upper else ("below" if price < em_lower else "inside")
        prev_em_side = prev_state.get("em_side") if same_day else None
        new_state["em_side"] = current_em_side
        if prev_em_side is not None and prev_em_side != current_em_side:
            if current_em_side in ("above", "below"):
                used_pct = abs(price - em_anchor) / straddle_price * 100 if straddle_price else None
                pct_note = f"，已用去当日预期波动的 {used_pct:.0f}%" if used_pct is not None else ""
                bound = em_upper if current_em_side == "above" else em_lower
                candidates.append((
                    f"Expected Move {'上沿' if current_em_side == 'above' else '下沿'}突破：现价 {price:.2f} "
                    f"{'>' if current_em_side == 'above' else '<'} {bound:.2f}（当日区间 {em_lower:.2f}~{em_upper:.2f}，"
                    f"ATM IV {atm_iv}%{pct_note}）", "expected_move", "expected_move"
                ))
            elif prev_em_side in ("above", "below"):
                candidates.append((f"价格回到 Expected Move 区间内（{em_lower:.2f}~{em_upper:.2f}）", "expected_move", "expected_move"))

    # ============ 条件 4（主力）：破位延续确认 —— 没反转就一直追，不设固定时限 ============
    active_breaks = prev_state.get("active_breaks", []) if same_day else []
    still_active = []
    for b in active_breaks:
        move_pct = pct_change(price, b["break_price"])
        if b["direction"] == "up":
            invalidated = price <= b["break_price"]  # 涨破后又跌回起点，论点作废
        else:
            invalidated = price >= b["break_price"]  # 跌破后又涨回起点，论点作废
        if invalidated:
            continue  # 直接丢弃，不再追踪
        if not b["fired"]:
            confirmed = (b["direction"] == "up" and move_pct >= CONTINUATION_THRESHOLD_PCT) or \
                        (b["direction"] == "down" and move_pct <= -CONTINUATION_THRESHOLD_PCT)
            if confirmed:
                dir_label = "上涨" if b["direction"] == "up" else "下跌"
                elapsed_min = (now - datetime.fromisoformat(b["break_time"])).total_seconds() / 60 if "break_time" in b else None
                time_note = f"，破位后 {elapsed_min:.0f} 分钟" if elapsed_min is not None else ""
                candidates.append((
                    f"破位延续确认：{b['level']} {'上破' if b['direction']=='up' else '下破'}后继续{dir_label} "
                    f"{abs(move_pct):.2f}%（破位价 {b['break_price']:.2f} → 现价 {price:.2f}{time_note}）",
                    "continuation", f"continuation_{b['level']}_{b['direction']}"
                ))
                b["fired"] = True
        still_active.append(b)
    for nb in new_breaks:
        nb["break_time"] = now.isoformat()
    still_active.extend(new_breaks)
    new_state["active_breaks"] = still_active

    # ============ 条件 5（兜底，取代原15分钟固定窗口）：价格里程碑追踪 ============
    # 不依赖任何穿越事件，也不设时间上限：维护一个参考点(pivot)，只要价格从参考点
    # 又走出 MOMENTUM_THRESHOLD_PCT%，就提醒一次并把参考点重置为当前价，继续追踪下一段。
    # 这样无论是"已经在某一侧持续涨跌"还是"触发过一次后继续延伸"，都能持续捕捉，
    # 且天然没有固定时间窗口带来的盲区（能同时接住急动和慢速阴跌）。
    pivot_price = prev_state.get("pivot_price") if same_day else None
    if pivot_price is None:
        new_state["pivot_price"] = price  # 当天第一次运行，建立初始参考点，不触发
    else:
        move_pct = pct_change(price, pivot_price)
        if move_pct >= MOMENTUM_THRESHOLD_PCT:
            candidates.append((
                f"价格里程碑：较上一参考点上涨 {move_pct:.2f}%（{pivot_price:.2f} → {price:.2f}）",
                "momentum", "momentum"
            ))
            new_state["pivot_price"] = price
        elif move_pct <= -MOMENTUM_THRESHOLD_PCT:
            candidates.append((
                f"价格里程碑：较上一参考点下跌 {abs(move_pct):.2f}%（{pivot_price:.2f} → {price:.2f}）",
                "momentum", "momentum"
            ))
            new_state["pivot_price"] = price
        else:
            new_state["pivot_price"] = pivot_price  # 未达阈值，参考点不变，继续累积

    # ============ 冷却时间过滤 ============
    crossed_messages = []
    for msg, ttype, ckey in candidates:
        if cooldown_ok(last_fired, ckey, now):
            crossed_messages.append((msg, ttype))
            last_fired[ckey] = now.isoformat()
        else:
            print(f"[冷却中，跳过] {msg[:40]}...")
    new_state["last_fired"] = last_fired

    # ============ 背景信息块 ============
    max_pain_strike = mp_data.get("max_pain_strike")
    max_pain_distance = mp_data.get("distance", {})
    pin_probability = mp_data.get("pin_probability")
    zero_dte_magnet = levels.get("zero_dte_magnet")

    background_lines = []
    if max_pain_strike is not None:
        dist_pct, dist_dir = max_pain_distance.get("percent"), max_pain_distance.get("direction")
        dist_note = f"，现价在其{dist_dir}方 {dist_pct}%" if dist_pct is not None else ""
        pin_note = f"，Pin Probability {pin_probability}/100" if pin_probability is not None else ""
        background_lines.append(f"Pin Point (Max Pain): {max_pain_strike}{dist_note}{pin_note}")
    if zero_dte_magnet is not None:
        background_lines.append(f"Zero DTE Magnet: {zero_dte_magnet:.2f}（当日0DTE资金流聚集点，与现价差 {price - zero_dte_magnet:+.2f}）")
    if em_upper is not None:
        remaining_pct = max(0, 100 - abs(price - em_anchor) / straddle_price * 100) if straddle_price else None
        remain_note = f"，当日预期波动还剩约 {remaining_pct:.0f}%" if remaining_pct is not None else ""
        background_lines.append(f"Expected Move: {em_lower:.2f} ~ {em_upper:.2f}{remain_note}")

    # ============ 发送 ============
    if crossed_messages:
        trigger_types = {t for _, t in crossed_messages}
        text = f"⚡ {SYMBOL} 监控提醒 · {now_et_str()}\n" + "\n".join(m for m, _ in crossed_messages)
        text += f"\n\n当前价: {price:.2f}"
        text += f"\nGamma Flip: {gf_value:.2f}" if gf_value else ""
        text += f"\nCall Wall: {levels.get('call_wall')}"
        text += f"\nPut Wall: {levels.get('put_wall')}"
        if background_lines:
            text += "\n\n" + "\n".join(background_lines)
        if regime and "regime" in trigger_types:
            text += f"\n\n背景：当前 {REGIME_LABEL.get(regime, regime)}（仅供参考，非交易建议）"
        elif regime and "level_cross" in trigger_types:
            text += f"\n\n背景：大环境 Regime 为 {regime}，但该行权价局部的做市商对冲方向可能与大环境不同，突破后走势请结合上方 OI 构成判断（仅供参考，非交易建议）"
        send_telegram(text)
        print("已发送提醒:\n" + text)
    elif not prev_state:
        baseline_text = (
            f"✅ {SYMBOL} 监控已启动 · {now_et_str()}\n当前价: {price:.2f}\n"
            f"Gamma Flip: {gf_value:.2f}\nCall Wall: {levels.get('call_wall')}\n"
            f"Put Wall: {levels.get('put_wall')}\nRegime: {regime}"
        )
        if background_lines:
            baseline_text += "\n\n" + "\n".join(background_lines)
        send_telegram(baseline_text)
        print("首次运行，已发送基线通知。")
    else:
        print(f"无触发事件（或全部在冷却中）。当前价 {price:.2f}")

    all_state[SYMBOL] = new_state
    save_state(all_state)


def main() -> None:
    force_run = os.environ.get("FORCE_RUN", "").lower() == "true"

    if not in_market_hours():
        print("非交易时段（窗口 9:30-15:45 ET），跳过本次触发。")
        return

    if force_run:
        print("强制测试模式：只跑一次检查，立即返回结果。")
        check_once()
        return

    poll_interval = float(os.environ.get("POLL_INTERVAL_SECONDS", "200"))
    loop_duration = float(os.environ.get("LOOP_DURATION_SECONDS", "780"))

    loop_start = time.monotonic()
    iteration = 0
    while True:
        iteration += 1
        elapsed = time.monotonic() - loop_start
        remaining_in_window = seconds_until_window_close()
        if elapsed >= loop_duration:
            print(f"已达单次触发内部循环上限（{loop_duration:.0f}秒），退出。")
            break
        if remaining_in_window <= 0:
            print("已到 15:45 ET 窗口关闭时间，退出。")
            break
        print(f"---- 第 {iteration} 次检查 ----")
        check_once()
        if elapsed + poll_interval >= loop_duration or remaining_in_window <= poll_interval:
            print("下一次检查将超出循环时间上限或窗口关闭时间，提前结束。")
            break
        time.sleep(poll_interval)


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print(f"运行出错: {e}", file=sys.stderr)
        raise
