"""
FlashAlpha 关键点位穿越监控 -> Telegram 推送
监控：价格是否穿越 Gamma Flip / Call Wall / Put Wall
"""

import json
import os
import sys
from datetime import datetime
from zoneinfo import ZoneInfo

import requests

# ---- 配置 ----
SYMBOL = os.environ.get("SYMBOL", "SPY")
FLASHALPHA_API_KEY = os.environ["FLASHALPHA_API_KEY"]
TELEGRAM_BOT_TOKEN = os.environ["TELEGRAM_BOT_TOKEN"]
TELEGRAM_CHAT_ID = os.environ["TELEGRAM_CHAT_ID"]

STATE_FILE = "state.json"
LEVELS_URL = f"https://lab.flashalpha.com/v1/exposure/levels/{SYMBOL}"
MAXPAIN_URL = f"https://lab.flashalpha.com/v1/maxpain/{SYMBOL}"
TELEGRAM_URL = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"

# 要监控的三条线：(展示名, state.json 中的字段名, levels 返回里的字段名)
WATCH_LEVELS = [
    ("Gamma Flip", "gamma_flip", "gamma_flip"),
    ("Call Wall", "call_wall", "call_wall"),
    ("Put Wall", "put_wall", "put_wall"),
]


def in_market_hours() -> bool:
    """只在美股常规交易时段（含前后5分钟余量）内真正执行，其余时间直接跳过，避免无意义调用。
    设置环境变量 FORCE_RUN=true 可以绕过这个判断，方便休市时手动测试。"""
    if os.environ.get("FORCE_RUN", "").lower() == "true":
        return True
    now_et = datetime.now(ZoneInfo("America/New_York"))
    if now_et.weekday() >= 5:  # 周六=5, 周日=6
        return False
    start = now_et.replace(hour=9, minute=25, second=0, microsecond=0)
    end = now_et.replace(hour=16, minute=5, second=0, microsecond=0)
    return start <= now_et <= end


def load_state() -> dict:
    if os.path.exists(STATE_FILE):
        with open(STATE_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    return {}


def save_state(state: dict) -> None:
    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False, indent=2)


def send_telegram(text: str) -> None:
    resp = requests.post(
        TELEGRAM_URL,
        json={"chat_id": TELEGRAM_CHAT_ID, "text": text},
        timeout=15,
    )
    resp.raise_for_status()


def side(price: float, level: float) -> str:
    return "above" if price >= level else "below"


def get_regime_context() -> str:
    """
    拉取 dealer gamma regime 作为背景参考，不改变触发逻辑，只丰富通知内容。
    negative_gamma：做市商对冲顺势而为，突破更容易延续（信号相对更值得留意）
    positive_gamma：做市商对冲逆势而为，突破容易被拉回（信号相对更弱，仅供参考）
    拿不到时静默返回空字符串，不影响主流程。
    """
    try:
        resp = requests.get(
            MAXPAIN_URL,
            headers={"X-Api-Key": FLASHALPHA_API_KEY},
            timeout=15,
        )
        resp.raise_for_status()
        data = resp.json()
        regime = data.get("regime")
        if regime == "negative_gamma":
            return "\n\n背景：当前 Negative Gamma（做市商顺势对冲，突破相对更容易延续，仅供参考，非交易建议）"
        elif regime == "positive_gamma":
            return "\n\n背景：当前 Positive Gamma（做市商逆势对冲，突破容易被拉回，仅供参考，非交易建议）"
        return ""
    except Exception:
        return ""


def main() -> None:
    if not in_market_hours():
        print("非交易时段，跳过本次执行。")
        return

    resp = requests.get(
        LEVELS_URL,
        headers={"X-Api-Key": FLASHALPHA_API_KEY},
        timeout=15,
    )
    resp.raise_for_status()
    data = resp.json()

    price = data["underlying_price"]
    levels = data["levels"]

    prev_state = load_state().get(SYMBOL, {})
    new_state = {"underlying_price": price, "as_of": data.get("as_of")}
    crossed_messages = []

    for label, state_key, level_key in WATCH_LEVELS:
        level_value = levels.get(level_key)
        if level_value is None:
            continue

        current_side = side(price, level_value)
        new_state[state_key] = current_side
        new_state[f"{state_key}_value"] = level_value

        prev_side = prev_state.get(state_key)
        if prev_side is not None and prev_side != current_side:
            direction = "向上突破" if current_side == "above" else "向下跌破"
            crossed_messages.append(
                f"{label} {direction} {level_value:.2f}（当前价 {price:.2f}）"
            )

    if crossed_messages:
        text = f"⚡ {SYMBOL} 点位穿越提醒\n" + "\n".join(crossed_messages)
        text += f"\n\n当前价: {price:.2f}"
        text += f"\nGamma Flip: {levels.get('gamma_flip')}"
        text += f"\nCall Wall: {levels.get('call_wall')}"
        text += f"\nPut Wall: {levels.get('put_wall')}"
        text += get_regime_context()
        send_telegram(text)
        print("已发送穿越通知:\n" + text)
    elif not prev_state:
        # 首次运行，只做基线记录，不算"穿越"
        send_telegram(
            f"✅ {SYMBOL} 监控已启动\n当前价: {price:.2f}\n"
            f"Gamma Flip: {levels.get('gamma_flip')}\n"
            f"Call Wall: {levels.get('call_wall')}\n"
            f"Put Wall: {levels.get('put_wall')}"
        )
        print("首次运行，已发送基线通知。")
    else:
        print(f"无穿越事件。当前价 {price:.2f}")

    all_state = load_state()
    all_state[SYMBOL] = new_state
    save_state(all_state)


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print(f"运行出错: {e}", file=sys.stderr)
        raise
