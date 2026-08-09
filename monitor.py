"""
FlashAlpha 关键点位/结构性指标监控 -> Telegram 推送
监控内容：
1. 价格是否穿越 Gamma Flip / Call Wall / Put Wall
2. Dealer Gamma Regime 是否翻转（positive_gamma <-> negative_gamma）
3. 价格是否突破当日 Expected Move 上下沿（锚点为当日首次运行时的价格 ± Straddle Price）
 
每种触发类型配独立的上下文说明，避免笼统的背景文案在不同场景下产生误导。
"""
 
import json
import os
import sys
from datetime import datetime
from zoneinfo import ZoneInfo
 
import requests
 
SYMBOL = os.environ.get("SYMBOL", "SPY")
FLASHALPHA_API_KEY = os.environ["FLASHALPHA_API_KEY"]
TELEGRAM_BOT_TOKEN = os.environ["TELEGRAM_BOT_TOKEN"]
TELEGRAM_CHAT_ID = os.environ["TELEGRAM_CHAT_ID"]
 
STATE_FILE = "state.json"
LEVELS_URL = f"https://lab.flashalpha.com/v1/exposure/levels/{SYMBOL}"
MAXPAIN_URL = f"https://lab.flashalpha.com/v1/maxpain/{SYMBOL}"
TELEGRAM_URL = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
 
WATCH_LEVELS = [
    ("Gamma Flip", "gamma_flip", "gamma_flip"),
    ("Call Wall", "call_wall", "call_wall"),
    ("Put Wall", "put_wall", "put_wall"),
]
 
REGIME_LABEL = {
    "negative_gamma": "Negative Gamma（做市商顺势对冲，趋势相对容易延续）",
    "positive_gamma": "Positive Gamma（做市商逆势对冲，大范围内波动相对容易被压制）",
}
 
 
def in_market_hours() -> bool:
    if os.environ.get("FORCE_RUN", "").lower() == "true":
        return True
    now_et = datetime.now(ZoneInfo("America/New_York"))
    if now_et.weekday() >= 5:
        return False
    start = now_et.replace(hour=9, minute=25, second=0, microsecond=0)
    end = now_et.replace(hour=16, minute=5, second=0, microsecond=0)
    return start <= now_et <= end
 
 
def today_et_str() -> str:
    return datetime.now(ZoneInfo("America/New_York")).strftime("%Y-%m-%d")
 
 
def now_et_str() -> str:
    return datetime.now(ZoneInfo("America/New_York")).strftime("%H:%M ET")
 
 
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
 
 
def side(price: float, level: float) -> str:
    return "above" if price >= level else "below"
 
 
def fetch(url: str) -> dict:
    resp = requests.get(url, headers={"X-Api-Key": FLASHALPHA_API_KEY}, timeout=15)
    resp.raise_for_status()
    return resp.json()
 
 
def oi_at_strike(mp_data: dict, strike: float) -> dict | None:
    """在 max_pain 的 oi_by_strike 表里查某个行权价的 Call/Put OI，找不到返回 None。"""
    for row in mp_data.get("oi_by_strike", []):
        if row.get("strike") == strike:
            return row
    return None
 
 
def is_top_oi_strike(mp_data: dict, strike: float, top_n: int = 5) -> bool:
    """判断某行权价是否在当前到期日 OI 最大的前 N 名内。"""
    rows = mp_data.get("oi_by_strike", [])
    if not rows:
        return False
    sorted_rows = sorted(rows, key=lambda r: r.get("total_oi", 0), reverse=True)
    top_strikes = {r["strike"] for r in sorted_rows[:top_n]}
    return strike in top_strikes
 
 
def main() -> None:
    if not in_market_hours():
        print("非交易时段，跳过本次执行。")
        return
 
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
    crossed_messages = []
 
    # ---- 条件 1：三条线穿越，每条附带具体上下文 ----
    for label, state_key, level_key in WATCH_LEVELS:
        level_value = levels.get(level_key)
        if level_value is None:
            continue
        current_side = side(price, level_value)
        new_state[state_key] = current_side
        new_state[f"{state_key}_value"] = level_value
        prev_side = prev_state.get(state_key) if same_day else None
 
        if prev_side is not None and prev_side != current_side:
            direction = "向上突破" if current_side == "above" else "向下跌破"
            overshoot = abs(price - level_value)
            msg = f"{label} {direction} {level_value:.2f}（当前价 {price:.2f}，超出 {overshoot:.2f}）"
 
            # Call Wall / Put Wall 额外查该行权价的 OI 构成，判断磁吸力度
            if label in ("Call Wall", "Put Wall"):
                oi_row = oi_at_strike(mp_data, level_value)
                if oi_row:
                    is_top = is_top_oi_strike(mp_data, level_value)
                    rank_note = "（当前到期日 OI 最集中的行权价之一，对冲压力较大）" if is_top else "（OI 不算最集中，对冲压力相对有限）"
                    msg += (
                        f"\n  该行权价持仓：Call {oi_row['call_oi']:,} / Put {oi_row['put_oi']:,}"
                        f" {rank_note}"
                    )
            crossed_messages.append((msg, "level_cross"))
 
    # ---- 条件 2：Regime 翻转 ----
    new_state["regime"] = regime
    prev_regime = prev_state.get("regime") if same_day else None
    if regime and prev_regime and regime != prev_regime:
        gamma_flip_val = levels.get("gamma_flip")
        dist = price - gamma_flip_val if gamma_flip_val else None
        dist_note = f"，现价距 Gamma Flip {dist:+.2f}" if dist is not None else ""
        crossed_messages.append((
            f"Gamma Regime 翻转：{prev_regime} → {regime}{dist_note}",
            "regime"
        ))
 
    # ---- 条件 3：Expected Move 上下沿突破（锚点=当日首次运行价格）----
    if same_day and "em_upper" in prev_state:
        em_upper = prev_state["em_upper"]
        em_lower = prev_state["em_lower"]
        em_anchor = prev_state["em_anchor"]
    elif straddle_price is not None:
        em_anchor = price
        em_upper = price + straddle_price
        em_lower = price - straddle_price
    else:
        em_anchor = em_upper = em_lower = None
 
    if em_upper is not None:
        new_state["em_anchor"] = em_anchor
        new_state["em_upper"] = em_upper
        new_state["em_lower"] = em_lower
 
        current_em_side = "above" if price > em_upper else ("below" if price < em_lower else "inside")
        prev_em_side = prev_state.get("em_side") if same_day else None
        new_state["em_side"] = current_em_side
 
        if prev_em_side is not None and prev_em_side != current_em_side:
            pct_used = abs(price - em_anchor) / straddle_price * 100 if straddle_price else None
            pct_note = f"，已用去当日预期波动的 {pct_used:.0f}%" if pct_used is not None else ""
            if current_em_side == "above":
                crossed_messages.append((
                    f"Expected Move 上沿突破：现价 {price:.2f} > 上沿 {em_upper:.2f}"
                    f"（当日区间 {em_lower:.2f}~{em_upper:.2f}，ATM IV {atm_iv}%{pct_note}）",
                    "expected_move"
                ))
            elif current_em_side == "below":
                crossed_messages.append((
                    f"Expected Move 下沿突破：现价 {price:.2f} < 下沿 {em_lower:.2f}"
                    f"（当日区间 {em_lower:.2f}~{em_upper:.2f}，ATM IV {atm_iv}%{pct_note}）",
                    "expected_move"
                ))
            elif prev_em_side in ("above", "below"):
                crossed_messages.append((
                    f"价格回到 Expected Move 区间内（{em_lower:.2f}~{em_upper:.2f}）",
                    "expected_move"
                ))
 
    # ---- 标准背景信息块：Max Pain（Pin Point）+ Zero DTE Magnet + Expected Move，每条消息都带上 ----
    max_pain_strike = mp_data.get("max_pain_strike")
    max_pain_distance = mp_data.get("distance", {})
    pin_probability = mp_data.get("pin_probability")
    zero_dte_magnet = levels.get("zero_dte_magnet")
 
    background_lines = []
    if max_pain_strike is not None:
        dist_pct = max_pain_distance.get("percent")
        dist_dir = max_pain_distance.get("direction")
        dist_note = f"，现价在其{dist_dir}方 {dist_pct}%" if dist_pct is not None else ""
        pin_note = f"，Pin Probability {pin_probability}/100" if pin_probability is not None else ""
        background_lines.append(f"Pin Point (Max Pain): {max_pain_strike}{dist_note}{pin_note}")
    if zero_dte_magnet is not None:
        magnet_dist = price - zero_dte_magnet
        background_lines.append(
            f"Zero DTE Magnet: {zero_dte_magnet:.2f}（当日0DTE资金流聚集点，与现价差 {magnet_dist:+.2f}）"
        )
    if em_upper is not None:
        remaining_pct = None
        if straddle_price:
            used = abs(price - em_anchor)
            remaining_pct = max(0, 100 - used / straddle_price * 100)
        remain_note = f"，当日预期波动还剩约 {remaining_pct:.0f}%" if remaining_pct is not None else ""
        background_lines.append(f"Expected Move: {em_lower:.2f} ~ {em_upper:.2f}{remain_note}")
 
    if crossed_messages:
        trigger_types = {t for _, t in crossed_messages}
        text = f"⚡ {SYMBOL} 监控提醒 · {now_et_str()}\n" + "\n".join(m for m, _ in crossed_messages)
        text += f"\n\n当前价: {price:.2f}"
        text += f"\nGamma Flip: {levels.get('gamma_flip'):.2f}"
        text += f"\nCall Wall: {levels.get('call_wall')}"
        text += f"\nPut Wall: {levels.get('put_wall')}"
 
        if background_lines:
            text += "\n\n" + "\n".join(background_lines)
 
        # 只在触发原因包含 regime 或 gamma flip 相关时才附加大环境背景，
        # 避免在纯粹的墙突破场景下误导（墙本身局部对冲方向可能与大环境相反）
        if regime and trigger_types & {"regime"}:
            text += f"\n\n背景：当前 {REGIME_LABEL.get(regime, regime)}（仅供参考，非交易建议）"
        elif regime and "level_cross" in trigger_types:
            text += (
                f"\n\n背景：大环境 Regime 为 {regime}，但该行权价局部的做市商对冲方向"
                f"可能与大环境不同，突破后走势请结合上方 OI 构成判断（仅供参考，非交易建议）"
            )
 
        send_telegram(text)
        print("已发送提醒:\n" + text)
    elif not prev_state:
        baseline_text = (
            f"✅ {SYMBOL} 监控已启动 · {now_et_str()}\n当前价: {price:.2f}\n"
            f"Gamma Flip: {levels.get('gamma_flip'):.2f}\n"
            f"Call Wall: {levels.get('call_wall')}\n"
            f"Put Wall: {levels.get('put_wall')}\n"
            f"Regime: {regime}"
        )
        if background_lines:
            baseline_text += "\n\n" + "\n".join(background_lines)
        send_telegram(baseline_text)
        print("首次运行，已发送基线通知。")
    else:
        print(f"无触发事件。当前价 {price:.2f}")
 
    all_state[SYMBOL] = new_state
    save_state(all_state)
 
 
if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print(f"运行出错: {e}", file=sys.stderr)
        raise
