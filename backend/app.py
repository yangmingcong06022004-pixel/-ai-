"""
马到橙功后端 v3.8
新增：美团行程闭环 Tool + 全景出行 Agent Tool + 周末出行 Agent Tool + 人格路线画像 + 最近米其林 + 多轮对话记忆
天气：Open-Meteo · 路线：百度地图 · AI：DeepSeek · RAG：米其林 ChromaDB
"""
import csv, json, os, threading, math, re, shutil, subprocess, sys, sqlite3, time, uuid, random
from concurrent.futures import ThreadPoolExecutor
from typing import Optional
from urllib.parse import quote
import requests
from flask import Flask, Response, jsonify, request, stream_with_context
from flask_cors import CORS

BASE_DIR = os.path.dirname(os.path.abspath(__file__))

try:
    import pandas as pd
except ImportError as e:
    pd = None
    print(f"⚠️  pandas 未安装，最近米其林地理排序暂不可用：{e}")

MICHELIN_IMPORT_ERROR = ""
try:
    from michelin_rag import load_rag, ask_michelin
    MICHELIN_AVAILABLE = True
    print("✅ michelin_rag 导入成功")
except Exception as e:
    MICHELIN_IMPORT_ERROR = str(e)
    print(f"⚠️  michelin_rag 导入失败：{e}")
    MICHELIN_AVAILABLE = False

app = Flask(__name__)
CORS(app)

BAIDU_AK          = "8tskCa9dm3m8i1DQvtPRW9AxSfB1cZKY"
BAIDU_RIDING_URL  = "https://api.map.baidu.com/directionlite/v1/riding"
BAIDU_WALKING_URL = "https://api.map.baidu.com/directionlite/v1/walking"
BAIDU_GEOCODE_URL = "https://api.map.baidu.com/geocoding/v3/"
BAIDU_PLACE_URL   = "https://api.map.baidu.com/place/v2/search"
OM_GEO_URL        = "https://geocoding-api.open-meteo.com/v1/search"
OM_WEATHER_URL    = "https://api.open-meteo.com/v1/forecast"
DEEPSEEK_API_KEY  = os.environ.get("DEEPSEEK_API_KEY", "")
DEEPSEEK_URL      = "https://api.deepseek.com/chat/completions"
DEEPSEEK_MODEL    = "deepseek-chat"
BAIDU_TRANSLATE_URL = "https://fanyi-api.baidu.com/ait/api/aiTextTranslate"
BAIDU_TRANSLATE_KEY = os.environ.get("BAIDU_TRANSLATE_KEY", "leVv_d8cn9iia4eo5ucr6cjp0")
CSV_PATH          = os.path.join(BASE_DIR, "rag_documents.csv")
REQUEST_TIMEOUT   = 10
DEEPSEEK_TIMEOUT  = 20
MEITUAN_SKILL_TIMEOUT = int(os.environ.get("MEITUAN_SKILL_TIMEOUT", "25"))
MEITUAN_TRAVEL_SKILL_DIR = os.path.join(BASE_DIR, "meituan-travel")
MEITUAN_VENUE_SKILL_DIR  = os.path.join(BASE_DIR, "meituan-venue-guide")
MEITUAN_COUPON_SKILL_DIR = os.path.join(BASE_DIR, "meituan-fenxiao-promotion-coupon")
MEITUAN_PAOTUI_SKILL_DIR = os.path.join(BASE_DIR, "mt-paotui")
HISTORY_DB_PATH = os.path.join(BASE_DIR, "chat_history.sqlite3")
HERMES_SKILL_NAME = "meituan-trip-agent"
HERMES_SKILL_PATH = os.path.expanduser(f"~/.hermes/skills/{HERMES_SKILL_NAME}/SKILL.md")
HERMES_PROJECT_SKILL_PATH = os.path.join(os.path.dirname(BASE_DIR), "hermes-agent-main", "skills", HERMES_SKILL_NAME, "SKILL.md")
SOUL_DIR = BASE_DIR
SOUL_IDENTITY_PATH = os.path.join(SOUL_DIR, "agent_identity.md")
SOUL_USER_PROFILE_PATH = os.path.join(SOUL_DIR, "user_profile.json")
SOUL_MEMORY_RULES_PATH = os.path.join(SOUL_DIR, "memory_rules.md")
PENDING_ORDERS = {}
MOCK_RESOURCE_MONITORS = {}
MOCK_MONITOR_LOCK = threading.Lock()

# ════════════════════════════════════════════════════════════════
# Task State 状态机  —  session 级别持久化
# ════════════════════════════════════════════════════════════════
_TASK_STATES: dict = {}          # session_id → TaskState dict
_TASK_STATE_LOCK = threading.Lock()

# ── 匹配表 ──────────────────────────────────────────────────────
_CHOICE_MAP: dict[str, int] = {
    "1": 0, "一": 0, "方案1": 0, "方案一": 0, "第一个": 0, "第1个": 0,
    "选1": 0, "选方案1": 0, "选择方案1": 0, "生成方案1": 0,
    "2": 1, "二": 1, "方案2": 1, "方案二": 1, "第二个": 1, "第2个": 1,
    "选2": 1, "选方案2": 1, "选择方案2": 1, "生成方案2": 1,
    "3": 2, "三": 2, "方案3": 2, "方案三": 2, "第三个": 2, "第3个": 2,
    "选3": 2, "选方案3": 2, "选择方案3": 2, "生成方案3": 2,
    "4": 3, "四": 3, "方案4": 3, "方案四": 3, "第四个": 3, "第4个": 3,
    "选4": 3, "选方案4": 3, "选择方案4": 3, "生成方案4": 3,
}
_CONFIRM_SET = {"确认", "就这个", "可以", "开始", "帮我订", "下单",
                "执行", "开始执行", "好的", "没问题", "ok", "OK", "好", "行",
                "确定", "是的", "就这样", "就这个了"}
_RESET_SET   = {"重新开始", "换个话题", "重新规划", "新规划", "算了",
                "取消", "重置", "清空", "不要了", "放弃"}
_RESET_ONLY_SET = {"重置", "清空", "重新开始", "换个话题"}

# 跟进词：用户在延续当前任务，必须绑定 CURRENT_TASK，禁止从历史猜城市
_FOLLOWUP_SET = {
    "查好了吗", "好了没", "查到了吗", "怎么样了", "结果呢", "有结果了吗",
    "继续", "继续吧", "继续规划", "继续查", "接着", "接着说", "然后呢",
    "生成方案", "生成行程", "出方案", "给我方案", "给方案", "出行程",
    "帮我查", "查一下", "查查", "搜一下", "再查一下",
    "好的继续", "ok继续", "OK继续",
}

# 新目的地模式：用户明确指定新目的地（比 _NEW_TASK_PAT 更全）
_NEW_DEST_PAT = re.compile(
    r"(?:我想去|帮我去|带我去|去|到|前往|规划|帮我规划|帮我安排|安排|出发去)"
    r"\s*([^\s，。！？,;；]{2,8})"
    r"(?:玩|旅游|旅行|看看|走走|游玩|一日游|两日游|三日游|周末游|出游|$)"
)

_INTENT_PAT = {
    "medicine_delivery": r"送药|药品|买药|药店|处方|医院",
    "hotel_booking":     r"酒店|住宿|民宿|宾馆",
    "restaurant":        r"餐厅|吃饭|美食|火锅|日料|馆子",
    "trip_planning":     r"行程|出游|旅游|旅行|规划|攻略",
    "flight":            r"机票|航班|飞机|起飞|落地",
    "route":             r"路线|骑行|步行|导航|怎么走",
    "shopping":          r"购物|商圈|买|逛街",
}
_CITY_PAT = (r"(北京|上海|杭州|广州|深圳|成都|重庆|西安|武汉|南京|苏州"
             r"|新加坡|厦门|三亚|香港|澳门|天津|青岛|大连|长沙|哈尔滨|沈阳)")
_NEW_TASK_PAT = re.compile(
    r"我想去.{1,10}(?:玩|旅游|看看|走走)|重新开始|换个话题|新规划|取消当前"
)

def _is_reset_only_message(text: str) -> bool:
    return str(text or "").strip() in _RESET_ONLY_SET

# ── CRUD ──────────────────────────────────────────────────────
def _get_task_state(session_id: str) -> dict:
    return dict(_TASK_STATES.get(session_id or "default", {}))

def _set_task_state(session_id: str, state: dict):
    state["updated_at"] = time.time()
    with _TASK_STATE_LOCK:
        _TASK_STATES[session_id or "default"] = state

def _clear_task_state(session_id: str):
    with _TASK_STATE_LOCK:
        _TASK_STATES.pop(session_id or "default", None)

# ── 跟进词检测 ─────────────────────────────────────────────────
def _is_followup_msg(msg: str, task_state: dict) -> bool:
    """判断用户输入是否为跟进指令，需要绑定 CURRENT_TASK。"""
    if not task_state or not task_state.get("active_city"):
        return False
    m = msg.strip()
    # 精确跟进词
    if m in _FOLLOWUP_SET:
        return True
    # 在任务进行中时，短于8字且不含新目的地 → 按跟进处理
    if (len(m) <= 8
            and task_state.get("status") not in ("idle", "completed", None)
            and not re.search(_CITY_PAT, m)):
        return True
    return False

# ── 新任务检测 ─────────────────────────────────────────────────
def _is_new_task(msg: str, task_state: dict) -> bool:
    """短输入默认延续；含新城市+意图或明确重置才开新任务。"""
    if not task_state or task_state.get("status", "idle") in ("idle", "completed"):
        return True
    m = msg.strip()
    # 跟进词 → 永远延续
    if _is_followup_msg(m, task_state):
        return False
    # 8字以内且无新目的地 → 延续
    if len(m) <= 8 and not re.search(_CITY_PAT, m):
        return False
    # 明确重置词
    if any(w in m for w in _RESET_SET):
        return True
    # 用户明确指定新目的地，且与当前任务城市不同
    dest_m = _NEW_DEST_PAT.search(m)
    if dest_m:
        new_place = dest_m.group(1)
        new_city_m = re.search(_CITY_PAT, new_place)
        new_city = new_city_m.group(1) if new_city_m else _city_alias(new_place)
        cur_city = task_state.get("active_city", "")
        if new_city and cur_city and new_city not in cur_city and cur_city not in new_city:
            return True
    # 消息里出现新城市 + 行程意图 → 新任务
    city_m2 = re.search(_CITY_PAT, m)
    if city_m2:
        new_city2 = city_m2.group(1)
        cur_city2 = task_state.get("active_city", "")
        intent_m = re.search(r"行程|出游|旅游|旅行|规划|攻略|游玩|玩|住|吃|景点", m)
        if intent_m and cur_city2 and new_city2 != cur_city2:
            return True
    return False

# ── 选项解析 ───────────────────────────────────────────────────
def _parse_options_from_text(text: str) -> list:
    """从 AI 回复解析 方案1/2/3，补充 option_id / summary / action_type / payload。"""
    num_map = {"1": 0, "2": 1, "3": 2, "4": 3,
               "一": 0, "二": 1, "三": 2, "四": 3}
    patterns = [
        r'方案\s*([1-4一二三四])\s*[：:、.。]\s*(.{4,80})',
        r'选项\s*([1-4一二三四])\s*[：:、.。]\s*(.{4,80})',
        r'(?:^|\n)\s*([1-4])\s*[.、）)]\s*(.{4,80})',
    ]
    seen, options = set(), []
    for pat in patterns:
        for m in re.finditer(pat, text, re.MULTILINE):
            n, label = m.group(1).strip(), m.group(2).strip()
            label = re.sub(r'\s+', ' ', label.split('\n')[0])[:80]
            idx = num_map.get(n, -1)
            if idx < 0 or idx in seen or not label:
                continue
            seen.add(idx)
            # 推断 action_type
            if re.search(r"机票|航班|飞机", label):
                act = "mock_flight_order"
            elif re.search(r"快递|邮寄|物流", label):
                act = "mock_delivery_order"
            elif re.search(r"酒店|住宿|民宿", label):
                act = "mock_hotel_order"
            elif re.search(r"打车|叫车|网约车", label):
                act = "mock_ride_order"
            elif re.search(r"查|搜|看|了解|咨询", label):
                act = "mock_search"
            else:
                act = "mock_plan_confirm"
            options.append({
                "option_id":   f"option_{idx+1}",
                "label":       label,
                "summary":     label[:40],
                "action_type": act,
                "payload":     {},
                "index":       idx,
            })
        if len(options) >= 2:
            break
    return sorted(options, key=lambda x: x["index"])[:4]

# ── 状态更新 ───────────────────────────────────────────────────
def _update_task_state_from_reply(session_id: str, user_msg: str, reply_text: str) -> dict:
    state = _get_task_state(session_id)
    if not state.get("active_task_id"):
        state["active_task_id"] = f"task_{uuid.uuid4().hex[:8]}"

    options = _parse_options_from_text(reply_text)
    if options:
        state["last_options"]        = options
        state["status"]              = "awaiting_choice"
        state["selected_option"]     = None
        state["pending_action"]      = None
    elif re.search(r'待确认动作|待确认订单|生成.*订单|Mock.*成功|已生成', reply_text):
        order_m = re.search(r'(ORD-\w+)', reply_text)
        state["pending_action"] = {
            "type": "confirm_order",
            "order_id": order_m.group(1) if order_m else "",
        }
        state["status"] = "awaiting_confirm"
    else:
        if state.get("status") not in ("awaiting_choice", "awaiting_confirm"):
            state["status"] = "planning"

    # 城市只从 user_msg 提取，禁止从 reply_text 提取（防止 AI 回复提到旧城市污染）
    city_m = re.search(_CITY_PAT, user_msg)
    if city_m:
        new_city = city_m.group(1)
        state["active_city"] = new_city
        state["active_destination"] = new_city
    # 意图从 user_msg 提取；只有 user_msg 无意图时才从 reply_text[:200] 补充
    _intent_found = False
    for intent, pat in _INTENT_PAT.items():
        if re.search(pat, user_msg):
            state["active_intent"] = intent
            _intent_found = True
            break
    if not _intent_found and not state.get("active_intent"):
        for intent, pat in _INTENT_PAT.items():
            if re.search(pat, reply_text[:200]):
                state["active_intent"] = intent
                break

    state["last_user_goal"] = user_msg[:120]
    _set_task_state(session_id, state)
    return state

# ── 短输入解析器（必须在 LLM 之前调用） ────────────────────────
def resolve_short_reply(raw_msg: str, task_state: dict,
                        action_type: str = "", option_id: str = "") -> dict | None:
    """
    规则拦截器：1/2/3/确认/就这个 直接走任务状态，不送给 DeepSeek。
    返回 None 表示不命中，继续走 LLM。
    """
    msg   = raw_msg.strip()
    if _is_reset_only_message(msg):
        return {"type": "reset_task"}
    if not task_state:
        return None
    status = task_state.get("status", "idle")
    opts   = task_state.get("last_options", [])

    # 0. 直接重置
    if _is_reset_only_message(msg):
        return {"type": "reset_task"}

    # 0.5. 跟进词：绑定 CURRENT_TASK，标记为 follow_up 交 LLM 处理
    if msg in _FOLLOWUP_SET and task_state.get("active_city"):
        return {"type": "followup_current_task",
                "current_city": task_state.get("active_city"),
                "last_goal": task_state.get("last_user_goal", "")}

    # 1. 前端直传 action_type=select_option + option_id（最稳）
    if action_type == "select_option" and option_id:
        opt = next((o for o in opts if o["option_id"] == option_id), None)
        if opt:
            return {"type": "select_option",
                    "selected_index": opt["index"],
                    "selected_option": opt}

    # 2. 文本命中选项编号（status == awaiting_choice）
    if status == "awaiting_choice" and opts and msg in _CHOICE_MAP:
        idx = _CHOICE_MAP[msg]
        if idx < len(opts):
            return {"type": "select_option",
                    "selected_index": idx,
                    "selected_option": opts[idx]}

    # 3. 确认动作（status == awaiting_confirm）
    if status == "awaiting_confirm" and msg in _CONFIRM_SET:
        return {"type": "confirm_current_action",
                "current_action": task_state.get("pending_action")}

    # 4. 任何状态下短输入的确认
    if msg in _CONFIRM_SET and task_state.get("pending_action"):
        return {"type": "confirm_current_action",
                "current_action": task_state.get("pending_action")}

    return None

# ── 解析结果执行 ───────────────────────────────────────────────
def _handle_resolved_action(resolved: dict, task_state: dict, session_id: str) -> dict:
    rtype = resolved.get("type")

    if rtype == "reset_task":
        _clear_task_state(session_id)
        return {"reply": "🍊 已重置当前任务，请告诉我你的新需求！", "task_state": {}}

    if rtype == "followup_current_task":
        # 返回 None 让调用方继续走 LLM，但已注入当前任务上下文
        return None

    if rtype == "select_option":
        opt  = resolved["selected_option"]
        idx  = resolved["selected_index"]
        new  = dict(task_state)
        new["selected_option"] = opt
        new["status"]          = "awaiting_confirm"
        new["pending_action"]  = {
            "type":        opt.get("action_type", "mock_plan_confirm"),
            "option_id":   opt.get("option_id", ""),
            "option_label": opt.get("label", ""),
            "payload":     opt.get("payload", {}),
        }
        _set_task_state(session_id, new)
        reply = (
            f"✅ 已选择方案{idx+1}：{opt['label']}\n\n"
            f"准备执行：{opt.get('summary','')}\n\n"
            f"说「确认」开始执行，或说「换一个」重新选择。"
        )
        return {"reply": reply, "task_state": new}

    if rtype == "confirm_current_action":
        action   = resolved.get("current_action") or {}
        order_id = action.get("order_id", "") if isinstance(action, dict) else ""
        opt_label = action.get("option_label", "") if isinstance(action, dict) else ""
        new = dict(task_state)
        new["status"]         = "completed"
        new["pending_action"] = None
        _set_task_state(session_id, new)
        detail = f"订单 {order_id} 已确认。" if order_id else (f"已执行：{opt_label}" if opt_label else "操作已确认。")
        reply = f"🍊 Mock 执行成功！{detail}\n\n如需继续规划请继续描述。"
        return {"reply": reply, "task_state": new}

    return {"reply": "🍊 收到，请继续。", "task_state": task_state}

# ── 传给 LLM 的干净上下文（只保留最近 6 轮 + 任务摘要） ────────
def _build_clean_history(history: list, task_state: dict) -> list:
    """只保留与当前任务相关的最近 6 轮，附加 CURRENT_TASK 锁定摘要。"""
    clean = []
    cur_city = task_state.get("active_city") or task_state.get("active_destination", "")

    # ── CURRENT_TASK 锁定摘要（始终注入，优先级最高） ──────────────
    if task_state and (task_state.get("active_city") or task_state.get("active_destination")):
        opts_text = ""
        if task_state.get("last_options"):
            opts_text = "候选方案：" + "；".join(
                f"方案{o['index']+1}={o['label']}" for o in task_state["last_options"]
            )
        summary = (
            f"[CURRENT_TASK_LOCK] "
            f"当前任务目的地={cur_city} "
            f"任务ID={task_state.get('active_task_id','')} "
            f"预算={task_state.get('active_budget','')} "
            f"天数={task_state.get('active_days','')} "
            f"意图={task_state.get('active_intent','')} "
            f"状态={task_state.get('status','')} "
            f"{opts_text} "
            f"用户目标={task_state.get('last_user_goal','')[:80]} "
            f"[规则：本次回复必须围绕以上目的地展开，禁止从历史对话中提取其他城市覆盖当前任务]"
        )
        clean.append({"role": "system", "content": summary})

    # ── 最近 6 轮，过滤含其他城市的旧轮次 ──────────────────────────
    valid = [h for h in (history or []) if h.get("role") in ("user", "assistant") and h.get("content")]
    recent = valid[-12:]  # 从最近12轮里筛

    kept = []
    for h in recent:
        content = h.get("content", "")
        if cur_city:
            # 该轮包含当前城市 → 保留（覆盖"从上海去厦门"这类含出发地的有效轮次）
            if cur_city in content:
                kept.append(h)
                continue
            # 该轮含其他城市但不含当前城市 → 过滤（旧任务污染）
            other_city = re.search(_CITY_PAT, content)
            if other_city and other_city.group(1) != cur_city:
                continue
        kept.append(h)

    for h in kept[-6:]:
        clean.append({"role": h["role"], "content": h["content"]})
    return clean

if MICHELIN_AVAILABLE:
    try:
        import michelin_rag as _michelin_rag_mod
        _michelin_rag_mod.CSV_PATH = CSV_PATH
        _michelin_rag_mod.VECTOR_DB_DIR = os.path.join(BASE_DIR, "chroma_db")
    except Exception as e:
        print(f"⚠️  RAG路径校准失败：{e}")

ROUTE_PROFILES = {
    "fast": {
        "icon": "⚡",
        "title": "推荐最快路线",
        "short": "最快",
        "road_prefer": 0,
        "duration_factor": 0.92,
        "features": ["最短时间", "最少停留", "高效率移动"],
        "strategy": "优先最短时间、少绕路、少停留，适合特种兵式高效率移动。",
    },
    "scenic": {
        "icon": "😌",
        "title": "推荐风景慢游路线",
        "short": "慢骑",
        "road_prefer": 3,
        "duration_factor": 1.18,
        "features": ["风景更好", "避开机动车道", "适合拍照休息"],
        "strategy": "优先舒适、风景、低压力移动，允许略微绕路和停留。",
    },
    "quiet": {
        "icon": "🌙",
        "title": "推荐安静路线",
        "short": "安静",
        "road_prefer": 3,
        "duration_factor": 1.06,
        "features": ["避开热门区域", "人流较少", "安静低压体验"],
        "strategy": "优先避开热门区域和高人流路段，降低社交压力。",
    },
    "budget": {
        "icon": "🎓",
        "title": "推荐省钱路线",
        "short": "省钱",
        "road_prefer": 3,
        "duration_factor": 1.10,
        "features": ["避免收费区域", "地铁步行友好", "补给点更多"],
        "strategy": "优先低成本、地铁/步行覆盖、平价补给点和高性价比。",
    },
}

PERSONA_PROFILES = {
    "relax": "scenic",
    "special": "fast",
    "special_force": "fast",
    "romantic": "scenic",
    "introvert": "quiet",
    "socialfear": "quiet",
    "social_fear": "quiet",
    "family": "quiet",
    "student": "budget",
    "elder": "quiet",
    "photo_hunter": "scenic",
    "foodie": "scenic",
}

PERSONA_LABELS = {
    "relax": "松弛感状态",
    "special": "特种兵模式",
    "special_force": "特种兵状态",
    "romantic": "情侣浪漫模式",
    "introvert": "i人模式",
    "socialfear": "社恐模式",
    "social_fear": "社恐状态",
    "family": "家庭状态",
    "student": "穷游大学生模式",
    "elder": "长辈友好状态",
    "photo_hunter": "出片党状态",
    "foodie": "美食脑袋状态",
}

PERSONA_ALIASES = {
    "special": "special_force",
    "socialfear": "social_fear",
    "introvert": "social_fear",
    "romantic": "photo_hunter",
}

PERSONA_WEIGHTS = {
    "relax": {"efficiency": 0.35, "comfort": 0.95, "crowd_avoidance": 0.75, "budget_sensitive": 0.45, "photo_value": 0.60, "food_priority": 0.65, "walking_tolerance": 0.40, "nightlife": 0.50},
    "special_force": {"efficiency": 0.98, "comfort": 0.30, "crowd_avoidance": 0.20, "budget_sensitive": 0.55, "photo_value": 0.45, "food_priority": 0.35, "walking_tolerance": 0.95, "nightlife": 0.80},
    "social_fear": {"efficiency": 0.55, "comfort": 0.85, "crowd_avoidance": 0.98, "budget_sensitive": 0.50, "photo_value": 0.55, "food_priority": 0.65, "walking_tolerance": 0.55, "nightlife": 0.20},
    "family": {"efficiency": 0.55, "comfort": 0.95, "crowd_avoidance": 0.70, "budget_sensitive": 0.70, "photo_value": 0.60, "food_priority": 0.80, "walking_tolerance": 0.35, "nightlife": 0.20},
    "student": {"efficiency": 0.75, "comfort": 0.45, "crowd_avoidance": 0.40, "budget_sensitive": 0.99, "photo_value": 0.78, "food_priority": 0.85, "walking_tolerance": 0.88, "nightlife": 0.75},
    "elder": {"efficiency": 0.40, "comfort": 0.98, "crowd_avoidance": 0.82, "budget_sensitive": 0.55, "photo_value": 0.30, "food_priority": 0.75, "walking_tolerance": 0.20, "nightlife": 0.05},
    "photo_hunter": {"efficiency": 0.45, "comfort": 0.65, "crowd_avoidance": 0.55, "budget_sensitive": 0.45, "photo_value": 0.99, "food_priority": 0.55, "walking_tolerance": 0.75, "nightlife": 0.92},
    "foodie": {"efficiency": 0.45, "comfort": 0.80, "crowd_avoidance": 0.35, "budget_sensitive": 0.55, "photo_value": 0.65, "food_priority": 0.99, "walking_tolerance": 0.65, "nightlife": 0.72},
}

if MICHELIN_AVAILABLE:
    def _bg():
        try: load_rag()
        except Exception as e: print(f"❌ RAG加载失败：{e}")
    threading.Thread(target=_bg, daemon=True).start()

# ══ 天气辅助 ══
WMO_ZH = {0:"晴",1:"晴间多云",2:"多云",3:"阴",45:"雾",48:"浓雾",
    51:"小毛毛雨",53:"毛毛雨",55:"大毛毛雨",61:"小雨",63:"中雨",65:"大雨",
    71:"小雪",73:"中雪",75:"大雪",77:"冰粒",80:"阵雨",81:"中阵雨",82:"强阵雨",
    85:"小阵雪",86:"大阵雪",95:"雷暴",96:"雷暴冰雹",99:"强雷暴冰雹"}

def _deg_to_dir(deg):
    return ["北","东北","东","东南","南","西南","西","西北"][round(float(deg)/45)%8]+"风"

def _kmh_to_level(kmh):
    v=float(kmh)
    for t,l in [(1,"0级"),(6,"1级"),(12,"2级"),(20,"3级"),(29,"4级"),(39,"5级"),(50,"6级"),(62,"7级")]:
        if v<t: return l
    return "8级+"

def _clean_markdown(text: str) -> str:
    """后端统一清理模型常见 Markdown 包装，保证前端输出清爽。"""
    s = str(text or "")
    s = re.sub(r"```(?:json|markdown|md|text)?\s*", "", s, flags=re.I)
    s = s.replace("```", "")
    s = re.sub(r"\*\*([^*]+)\*\*", r"\1", s)
    s = re.sub(r"__([^_]+)__", r"\1", s)
    s = re.sub(r"^\s{0,3}#{1,6}\s+", "", s, flags=re.M)
    return s.strip()

def _safe_error_text(err) -> str:
    s = str(err or "")
    s = re.sub(r"([?&](?:ak|key|app_key|token|sign|access_token)=)[^&\s)]+", r"\1***", s, flags=re.I)
    s = re.sub(r"((?:AK|KEY|TOKEN|SECRET|API_KEY)\s*[=:]\s*)[^\s,;]+", r"\1***", s, flags=re.I)
    s = re.sub(r"(Bearer\s+)[A-Za-z0-9._-]+", r"\1***", s, flags=re.I)
    return s

def _read_text_file(path: str, default: str = "") -> str:
    try:
        with open(path, "r", encoding="utf-8") as f:
            return f.read().strip()
    except Exception:
        return default

def _ensure_soul_files():
    os.makedirs(SOUL_DIR, exist_ok=True)
    if not os.path.exists(SOUL_IDENTITY_PATH):
        with open(SOUL_IDENTITY_PATH, "w", encoding="utf-8") as f:
            f.write("你是马到橙功的橙管家，一个能根据用户人格、预算、时间和美团搜索，自动完成短途出游路线、吃喝玩乐、预算拆分和动态兜底的 AI 生活管家。")
    if not os.path.exists(SOUL_MEMORY_RULES_PATH):
        with open(SOUL_MEMORY_RULES_PATH, "w", encoding="utf-8") as f:
            f.write("本轮用户明确表达 > Soul 长期记忆 > 表单默认值 > 系统默认值。")
    if not os.path.exists(SOUL_USER_PROFILE_PATH):
        with open(SOUL_USER_PROFILE_PATH, "w", encoding="utf-8") as f:
            json.dump({
                "schema_version": "1.0",
                "user_name": "用户",
                "stable_preferences": {
                    "food": {"avoid_spicy": True, "avoid": ["辣"], "prefer": []},
                    "budget": {"default_max_total": 20000, "hotel_nightly_cap": None},
                    "transport": {"prefer": ["地铁"], "avoid": []},
                    "travel": {
                        "default_personas": ["relax"],
                        "common_personas": ["relax"],
                        "pace": "不赶路，路线顺、少折返。",
                        "likes_photo": None,
                        "likes_quiet": None,
                        "with_elder": False,
                        "with_children": False,
                        "queue_tolerance_minutes": 20,
                        "walking_intensity": "low",
                        "frequent_cities": [],
                    },
                },
                "memories": [],
            }, f, ensure_ascii=False, indent=2)

def _load_soul_user_profile() -> dict:
    _ensure_soul_files()
    try:
        with open(SOUL_USER_PROFILE_PATH, "r", encoding="utf-8") as f:
            profile = json.load(f)
        if not isinstance(profile, dict):
            raise ValueError("profile must be object")
        profile.setdefault("stable_preferences", {})
        profile.setdefault("memories", [])
        return profile
    except Exception as e:
        print(f"⚠️  Soul用户记忆读取失败：{_safe_error_text(e)}")
        return {"schema_version": "1.0", "stable_preferences": {}, "memories": []}

def _save_soul_user_profile(profile: dict):
    _ensure_soul_files()
    tmp = SOUL_USER_PROFILE_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(profile, f, ensure_ascii=False, indent=2)
    os.replace(tmp, SOUL_USER_PROFILE_PATH)

def _soul_memory_summary(profile: dict = None) -> str:
    profile = profile or _load_soul_user_profile()
    prefs = profile.get("stable_preferences", {})
    food = prefs.get("food", {})
    budget = prefs.get("budget", {})
    transport = prefs.get("transport", {})
    travel = prefs.get("travel", {})
    bits = []
    if food.get("avoid_spicy"):
        bits.append("不吃辣")
    avoid = [x for x in food.get("avoid", []) if x]
    if avoid:
        bits.append("忌口：" + "、".join(dict.fromkeys(avoid)))
    prefer_food = [x for x in food.get("prefer", []) if x]
    if prefer_food:
        bits.append("偏好：" + "、".join(dict.fromkeys(prefer_food)))
    if budget.get("default_max_total"):
        bits.append(f"默认总预算不超过{budget.get('default_max_total')}元")
    if budget.get("hotel_nightly_cap"):
        bits.append(f"酒店单晚不超过{budget.get('hotel_nightly_cap')}元")
    if transport.get("prefer"):
        bits.append("交通偏好：" + "、".join(dict.fromkeys(transport.get("prefer", []))))
    if transport.get("avoid"):
        bits.append("交通避免：" + "、".join(dict.fromkeys(transport.get("avoid", []))))
    if travel.get("pace"):
        bits.append("节奏：" + travel.get("pace"))
    if travel.get("likes_photo") is True:
        bits.append("喜欢拍照/出片")
    elif travel.get("likes_photo") is False:
        bits.append("不以拍照为优先")
    if travel.get("likes_quiet") is True:
        bits.append("偏好安静、人少")
    elif travel.get("likes_quiet") is False:
        bits.append("可接受热闹")
    if travel.get("with_elder"):
        bits.append("常带老人/长辈")
    if travel.get("with_children"):
        bits.append("常带孩子/亲子")
    if travel.get("queue_tolerance_minutes") is not None:
        bits.append(f"排队容忍约{travel.get('queue_tolerance_minutes')}分钟")
    if travel.get("walking_intensity"):
        intensity_label = {"low": "低步行强度", "medium": "中等步行强度", "high": "高步行强度"}.get(travel.get("walking_intensity"), travel.get("walking_intensity"))
        bits.append(intensity_label)
    if travel.get("frequent_cities"):
        bits.append("常去城市：" + "、".join(dict.fromkeys(travel.get("frequent_cities", []))))
    if travel.get("common_personas"):
        labels = [PERSONA_LABELS.get(_normalize_persona_key(str(x)), str(x)) for x in travel.get("common_personas", [])]
        bits.append("常用状态：" + "、".join(dict.fromkeys(labels)))
    return "；".join(bits) if bits else "暂无稳定偏好"

def _append_soul_memory(profile: dict, key: str, value: str, source: str = "user", confidence: float = 0.82):
    memories = profile.setdefault("memories", [])
    now = int(time.time())
    for item in memories:
        if item.get("key") == key:
            item.update({"value": value, "source": source, "confidence": confidence, "updated_at": now})
            return
    memories.append({"key": key, "value": value, "source": source, "confidence": confidence, "updated_at": now})

def _add_unique_pref(container: dict, field: str, value: str):
    arr = container.setdefault(field, [])
    if value not in arr:
        arr.append(value)

def _set_common_persona(travel: dict, persona_key: str):
    k = _normalize_persona_key(persona_key)
    if k in PERSONA_WEIGHTS:
        arr = travel.setdefault("common_personas", [])
        if k not in arr:
            arr.append(k)
        travel["default_personas"] = arr[:3]

def _extract_known_cities(segment: str) -> list:
    s = str(segment or "")
    found = []
    for city in sorted(CITY_GEO_INDEX, key=len, reverse=True):
        if city in s and city not in found:
            found.append(city)
    return found[:8]

def _parse_soul_money(raw: str) -> int:
    s = str(raw or "").strip()
    m = re.search(r"([0-9]+(?:\.[0-9]+)?)\s*万", s)
    if m:
        return int(float(m.group(1)) * 10000)
    m = re.search(r"([0-9]{2,7})", s)
    if m:
        return int(m.group(1))
    zh_map = {"一": 1, "二": 2, "两": 2, "三": 3, "四": 4, "五": 5, "六": 6, "七": 7, "八": 8, "九": 9, "十": 10}
    m = re.search(r"([一二两三四五六七八九十]+)\s*万", s)
    if m:
        val = 0
        token = m.group(1)
        if "十" in token:
            left, _, right = token.partition("十")
            val = (zh_map.get(left, 1) * 10) + zh_map.get(right, 0)
        else:
            val = zh_map.get(token, 0)
        return val * 10000 if val else 0
    return 0

def _update_soul_memory_from_message(text: str) -> dict:
    s = str(text or "")
    profile = _load_soul_user_profile()
    prefs = profile.setdefault("stable_preferences", {})
    updated = []
    food = prefs.setdefault("food", {})
    budget = prefs.setdefault("budget", {})
    transport = prefs.setdefault("transport", {})
    travel = prefs.setdefault("travel", {})
    if re.search(r"不吃辣|不能吃辣|不要辣|忌辣|少辣|微辣也不行", s):
        food["avoid_spicy"] = True
        _add_unique_pref(food, "avoid", "辣")
        _append_soul_memory(profile, "food.avoid_spicy", "用户不吃辣")
        updated.append("不吃辣")
    if re.search(r"不吃香菜|不要香菜|忌香菜", s):
        _add_unique_pref(food, "avoid", "香菜")
        _append_soul_memory(profile, "food.avoid_coriander", "用户不吃香菜")
        updated.append("不吃香菜")
    m_budget = re.search(r"(?:预算|总预算|控制在|不超过|以内|上限|希望.*?预算).*?([0-9]+(?:\.[0-9]+)?\s*万|[0-9]{3,7}|[一二两三四五六七八九十]+\s*万)", s)
    if m_budget:
        amount = _parse_soul_money(m_budget.group(1))
        if amount:
            budget["default_max_total"] = amount
            _append_soul_memory(profile, "budget.default_max_total", f"默认总预算不超过{amount}元")
            updated.append(f"预算{amount}元以内")
    m_hotel = re.search(r"(?:酒店|住宿|房间).*?(?:单晚|每晚|一晚|不要超过|不超过|以内).*?([0-9]{2,6})", s)
    if m_hotel:
        cap = int(m_hotel.group(1))
        budget["hotel_nightly_cap"] = cap
        _append_soul_memory(profile, "budget.hotel_nightly_cap", f"酒店单晚不超过{cap}元")
        updated.append(f"酒店单晚{cap}元以内")
    if re.search(r"喜欢坐地铁|地铁优先|优先地铁|坐地铁|多坐地铁", s):
        _add_unique_pref(transport, "prefer", "地铁")
        _append_soul_memory(profile, "transport.prefer", "城市内交通地铁优先")
        updated.append("地铁优先")
    if re.search(r"不想打车|不要打车|少打车|尽量不打车", s):
        _add_unique_pref(transport, "avoid", "打车")
        _append_soul_memory(profile, "transport.avoid_taxi", "尽量少打车")
        updated.append("少打车")
    if re.search(r"不想太累|别太累|松弛|慢一点|不赶|轻松一点", s):
        _set_common_persona(travel, "relax")
        travel["pace"] = "不赶路，路线顺、少折返、保留机动时间。"
        _append_soul_memory(profile, "travel.pace", "偏好松弛低压力行程")
        updated.append("松弛低压力")
    if re.search(r"喜欢拍照|爱拍照|想出片|出片|机位|日落|夜景|拍照好看", s):
        travel["likes_photo"] = True
        _set_common_persona(travel, "photo_hunter")
        _append_soul_memory(profile, "travel.likes_photo", "喜欢拍照/出片")
        updated.append("喜欢拍照")
    elif re.search(r"不拍照|不喜欢拍照|拍照不重要|不用出片", s):
        travel["likes_photo"] = False
        _append_soul_memory(profile, "travel.likes_photo", "不以拍照为优先")
        updated.append("不重拍照")
    if re.search(r"喜欢安静|安静一点|人少|小众|避开人群|不想人多|别太吵|低社交", s):
        travel["likes_quiet"] = True
        _set_common_persona(travel, "social_fear")
        _append_soul_memory(profile, "travel.likes_quiet", "偏好安静、人少、低社交压力")
        updated.append("喜欢安静")
    elif re.search(r"喜欢热闹|热闹一点|不怕人多", s):
        travel["likes_quiet"] = False
        _append_soul_memory(profile, "travel.likes_quiet", "可接受热闹场景")
        updated.append("可接受热闹")
    if re.search(r"带老人|带长辈|带爸妈|带父母|和爸妈|和父母|老人一起", s):
        travel["with_elder"] = True
        _set_common_persona(travel, "elder")
        _append_soul_memory(profile, "travel.with_elder", "出行可能带老人/长辈")
        updated.append("带老人")
    if re.search(r"带孩子|带娃|亲子|小朋友|儿童|推车|婴儿", s):
        travel["with_children"] = True
        _set_common_persona(travel, "family")
        _append_soul_memory(profile, "travel.with_children", "出行可能带孩子/亲子")
        updated.append("带孩子")
    m_queue = re.search(r"(?:排队|等位).*?(?:不要超过|不超过|最多|控制在|接受|能接受)?\s*([0-9]{1,3})\s*(?:分钟|min)", s)
    if m_queue:
        minutes = max(0, min(180, int(m_queue.group(1))))
        travel["queue_tolerance_minutes"] = minutes
        _append_soul_memory(profile, "travel.queue_tolerance_minutes", f"排队容忍约{minutes}分钟")
        updated.append(f"排队{minutes}分钟内")
    elif re.search(r"不想排队|不要排队|不排队|排队很烦|讨厌排队", s):
        travel["queue_tolerance_minutes"] = 5
        _append_soul_memory(profile, "travel.queue_tolerance_minutes", "排队容忍很低，约5分钟")
        updated.append("低排队容忍")
    if re.search(r"少走路|不想走太多|别走太多|步行少|腿脚|少步行", s):
        travel["walking_intensity"] = "low"
        _append_soul_memory(profile, "travel.walking_intensity", "低步行强度")
        updated.append("低步行强度")
    elif re.search(r"可以多走|能走路|暴走|多走点|高强度|特种兵", s):
        travel["walking_intensity"] = "high"
        _set_common_persona(travel, "special_force")
        _append_soul_memory(profile, "travel.walking_intensity", "高步行强度")
        updated.append("高步行强度")
    elif re.search(r"步行适中|中等步行|正常走", s):
        travel["walking_intensity"] = "medium"
        _append_soul_memory(profile, "travel.walking_intensity", "中等步行强度")
        updated.append("中等步行强度")
    m_cities = re.search(r"(?:常去|经常去|常玩的城市|常去城市(?:是|有)?)([^。！？\n]{2,60})", s)
    if m_cities:
        cities = _extract_known_cities(m_cities.group(1))
        for city in cities:
            _add_unique_pref(travel, "frequent_cities", city)
        if cities:
            _append_soul_memory(profile, "travel.frequent_cities", "常去城市：" + "、".join(cities))
            updated.append("常去城市：" + "、".join(cities))
    persona_hits = _auto_detect_personas(s)
    if persona_hits and re.search(r"常用|默认|一般|平时|喜欢.*模式|偏好.*模式", s):
        for key in persona_hits[:3]:
            _set_common_persona(travel, key)
        labels = [PERSONA_LABELS.get(k, k) for k in persona_hits[:3]]
        _append_soul_memory(profile, "travel.common_personas", "常用状态：" + "、".join(labels))
        updated.append("常用状态：" + "、".join(labels))
    if updated:
        _save_soul_user_profile(profile)
    return {"updated": bool(updated), "updated_keys": updated, "summary": _soul_memory_summary(profile)}

def _soul_default_personas() -> list:
    prefs = _load_soul_user_profile().get("stable_preferences", {})
    travel = prefs.get("travel", {})
    vals = travel.get("common_personas") or travel.get("default_personas", [])
    if isinstance(vals, str):
        vals = [vals]
    keys = []
    for item in vals:
        k = _normalize_persona_key(str(item))
        if k in PERSONA_WEIGHTS and k not in keys:
            keys.append(k)
    return keys or ["relax"]

def _soul_context(user_message: str = "") -> str:
    profile = _load_soul_user_profile()
    prefs = profile.get("stable_preferences", {})
    identity = _read_text_file(SOUL_IDENTITY_PATH, "你是马到橙功的私人出行管家。")
    rules = _read_text_file(SOUL_MEMORY_RULES_PATH, "本轮用户明确表达优先于长期记忆。")
    return (
        "## Soul 管家人格与长期记忆\n"
        f"{identity}\n\n"
        f"当前用户长期偏好：{_soul_memory_summary(profile)}\n"
        f"偏好JSON：{json.dumps(prefs, ensure_ascii=False)}\n\n"
        f"记忆使用规则：\n{rules}\n\n"
        f"本轮用户消息最高优先级：{str(user_message or '')[:500]}"
    )

def _simple_translate_fallback(text: str, target_lang: str) -> str:
    """无 DeepSeek Key 时的轻量输入辅助，不伪装成完整机器翻译。"""
    s = str(text or "").strip()
    if target_lang == "en":
        repl = {
            "我想去": "I want to visit ",
            "帮我": "please help me ",
            "做规划": "plan the itinerary",
            "行程规划": "itinerary plan",
            "预算": "budget ",
            "天": " days",
            "酒店": "hotel",
            "美团": "Meituan",
            "不要": "do not ",
            "不想": "do not want to ",
        }
    else:
        repl = {
            "I want to visit": "我想去",
            "please help me": "请帮我",
            "plan the itinerary": "做行程规划",
            "itinerary": "行程",
            "budget": "预算",
            "days": "天",
            "hotel": "酒店",
            "Meituan": "美团",
        }
    for a, b in repl.items():
        s = s.replace(a, b)
    return s

def _history_conn():
    conn = sqlite3.connect(HISTORY_DB_PATH, timeout=5)
    conn.row_factory = sqlite3.Row
    return conn

def _init_history_db():
    with _history_conn() as conn:
        conn.execute("""
            CREATE TABLE IF NOT EXISTS chat_messages (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                session_id TEXT NOT NULL DEFAULT 'default',
                role TEXT NOT NULL,
                content TEXT NOT NULL,
                city TEXT DEFAULT '',
                persona TEXT DEFAULT '',
                lang TEXT DEFAULT 'zh',
                created_at INTEGER NOT NULL
            )
        """)
        conn.execute("CREATE INDEX IF NOT EXISTS idx_chat_messages_created ON chat_messages(created_at DESC)")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_chat_messages_session ON chat_messages(session_id, created_at DESC)")
        try:
            conn.execute("""
                CREATE VIRTUAL TABLE IF NOT EXISTS chat_messages_fts
                USING fts5(content, role, city, persona, content='chat_messages', content_rowid='id')
            """)
            conn.execute("""
                CREATE TRIGGER IF NOT EXISTS chat_messages_ai AFTER INSERT ON chat_messages BEGIN
                    INSERT INTO chat_messages_fts(rowid, content, role, city, persona)
                    VALUES (new.id, new.content, new.role, new.city, new.persona);
                END
            """)
            conn.execute("""
                CREATE TRIGGER IF NOT EXISTS chat_messages_ad AFTER DELETE ON chat_messages BEGIN
                    INSERT INTO chat_messages_fts(chat_messages_fts, rowid, content, role, city, persona)
                    VALUES('delete', old.id, old.content, old.role, old.city, old.persona);
                END
            """)
        except Exception as e:
            print(f"⚠️  历史全文检索不可用，使用 LIKE 兜底：{e}")

def _save_history_message(role: str, content: str, city: str = "",
                          persona: str = "", session_id: str = "default",
                          lang: str = "zh") -> dict:
    text = _clean_markdown(content)
    if not text:
        return {}
    now = int(time.time())
    with _history_conn() as conn:
        cur = conn.execute(
            "INSERT INTO chat_messages(session_id, role, content, city, persona, lang, created_at) VALUES (?,?,?,?,?,?,?)",
            (session_id or "default", role or "assistant", text[:8000], city or "", persona or "", lang or "zh", now),
        )
        return {"id": cur.lastrowid, "created_at": now}

def _search_history(q: str = "", limit: int = 30) -> list:
    q = (q or "").strip()
    limit = max(1, min(int(limit or 30), 80))
    with _history_conn() as conn:
        if q:
            rows = []
            try:
                rows = conn.execute("""
                    SELECT m.* FROM chat_messages_fts f
                    JOIN chat_messages m ON m.id = f.rowid
                    WHERE chat_messages_fts MATCH ?
                    ORDER BY rank
                    LIMIT ?
                """, (q, limit)).fetchall()
            except Exception:
                rows = []
            if not rows:
                like = f"%{q}%"
                rows = conn.execute("""
                    SELECT * FROM chat_messages
                    WHERE content LIKE ? OR city LIKE ? OR persona LIKE ?
                    ORDER BY created_at DESC
                    LIMIT ?
                """, (like, like, like, limit)).fetchall()
        else:
            rows = conn.execute("SELECT * FROM chat_messages ORDER BY created_at DESC LIMIT ?", (limit,)).fetchall()
    return [dict(r) for r in rows]

_init_history_db()
_ensure_soul_files()

def _normalize_persona_key(key: str) -> str:
    k = (key or "").strip().lower()
    return PERSONA_ALIASES.get(k, k)

def _persona_keys(persona: str = "", prompt: str = "") -> list:
    raw = []
    if isinstance(persona, str):
        raw.extend([x for x in re.split(r"[,，+/、\s]+", persona) if x])
    elif isinstance(persona, list):
        raw.extend(persona)
    keys = []
    for item in raw:
        k = _normalize_persona_key(str(item))
        if k in PERSONA_WEIGHTS and k not in keys:
            keys.append(k)
    if not keys:
        keys = _auto_detect_personas(prompt)
    if not keys:
        keys = _soul_default_personas()
    return keys or ["relax"]

def _auto_detect_personas(prompt: str) -> list:
    s = str(prompt or "")
    rules = [
        ("special_force", r"特种兵|高效|多景点|极限|塞满|全部都去|赶时间|暴走"),
        ("social_fear", r"社恐|不想.*说话|低调|不互动|不想.*人多|人太多|避开.*人群|安静|小众|不想排队"),
        ("family", r"亲子|带娃|孩子|老人小孩|全家|家庭|婴儿|推车"),
        ("elder", r"老人|长辈|爸妈|父母|少走路|腿脚|无障碍|别太累"),
        ("student", r"穷|学生|省钱|便宜|预算少|平价|性价比|免费"),
        ("photo_hunter", r"情侣|女朋友|男朋友|约会|浪漫|出片|拍照|机位|日落|夜景|打卡|好看|审美|滤镜"),
        ("foodie", r"美食|吃|餐厅|小吃|夜市|米其林|本地菜|早餐|甜品|咖啡"),
        ("relax", r"不想太累|别太累|松弛|慢|不赶|舒适|放松|随意|慢逛|休息"),
    ]
    return [key for key, pattern in rules if re.search(pattern, s)][:3]

def _persona_state(persona: str = "", prompt: str = "") -> dict:
    keys = _persona_keys(persona, prompt)
    merged = {}
    for metric in ("efficiency", "comfort", "crowd_avoidance", "budget_sensitive", "photo_value", "food_priority", "walking_tolerance", "nightlife"):
        vals = [PERSONA_WEIGHTS[k][metric] for k in keys if k in PERSONA_WEIGHTS]
        merged[metric] = round(sum(vals) / len(vals), 2) if vals else 0
    dominant = max(keys, key=lambda k: max(PERSONA_WEIGHTS.get(k, {}).values() or [0])) if keys else "relax"
    return {
        "keys": keys,
        "dominant": dominant,
        "labels": [PERSONA_LABELS.get(k, k) for k in keys],
        "weights": merged,
    }

def _resolve_route_profile(route_profile: str = "", persona: str = "") -> str:
    rp = (route_profile or "").strip().lower()
    if rp in ROUTE_PROFILES:
        return rp
    keys = _persona_keys(persona)
    if "special_force" in keys:
        return "fast"
    if "student" in keys:
        return "budget"
    if any(k in keys for k in ("social_fear", "family", "elder")):
        return "quiet"
    return PERSONA_PROFILES.get(keys[0], "scenic")

def _route_profile_meta(route_profile: str, base_duration_min: int = 0) -> dict:
    rp = _resolve_route_profile(route_profile)
    cfg = ROUTE_PROFILES[rp]
    eta = round(base_duration_min * cfg["duration_factor"]) if base_duration_min else 0
    return {
        "profile": rp,
        "icon": cfg["icon"],
        "short": cfg["short"],
        "title": cfg["title"],
        "features": cfg["features"],
        "strategy": cfg["strategy"],
        "duration_min": eta,
        "road_prefer": cfg["road_prefer"],
    }

def _build_route_profiles(base_duration_min: int, active_profile: str = "") -> dict:
    profiles = {k: _route_profile_meta(k, base_duration_min) for k in ROUTE_PROFILES}
    rp = _resolve_route_profile(active_profile)
    if rp in profiles:
        profiles[rp]["duration_min"] = base_duration_min
    return profiles

def _route_context(persona: str, route_profile: str, route_strategy: str = "") -> str:
    rp = _resolve_route_profile(route_profile, persona)
    cfg = ROUTE_PROFILES[rp]
    persona_label = " + ".join(_persona_state(persona).get("labels") or ["未指定状态"])
    strategy = route_strategy or cfg["strategy"]
    return (
        f"当前出游状态：{persona_label}\n"
        f"当前路线方案：{cfg['icon']} {cfg['title']}\n"
        f"路线策略：{strategy}\n"
        "重要规则：不要固定单一路线。Agent 先按人格自动推荐路线方案，"
        "同时保持用户可切换 fast/scenic/quiet/budget 对应的最快、慢骑、安静、省钱路线。"
    )

def _optional_int(value, default=None):
    if value is None or value == "":
        return default
    try:
        return int(value)
    except (TypeError, ValueError):
        return default

def geocode_openmeteo(city: str) -> Optional[dict]:
    try:
        r=requests.get(OM_GEO_URL,params={"name":city,"count":1,"language":"zh","format":"json"},timeout=REQUEST_TIMEOUT)
        r.raise_for_status()
        res=r.json().get("results")
        if res:
            loc=res[0]
            return {"lat":loc["latitude"],"lng":loc["longitude"],"name":loc.get("name",city),"country":loc.get("country","")}
    except Exception as e: print(f"[om_geo]{_safe_error_text(e)}")
    return None

def geocode_baidu(address: str, city: str = "") -> Optional[dict]:
    try:
        r=requests.get(BAIDU_GEOCODE_URL,params={"address":address,"city":city,"output":"json","ak":BAIDU_AK},timeout=REQUEST_TIMEOUT)
        d=r.json()
        if d.get("status")==0:
            loc=d["result"]["location"]
            return {"lat":loc["lat"],"lng":loc["lng"]}
    except Exception as e: print(f"[baidu_geo]{_safe_error_text(e)}")
    return None

def search_baidu_place(query: str, city: str = "", limit: int = 3) -> list:
    """百度地点检索：用于周末 Agent 的真实基础 POI 坐标校准。"""
    try:
        r = requests.get(BAIDU_PLACE_URL, params={
            "query": query, "region": city or "全国", "output": "json",
            "scope": 2, "page_size": min(limit, 10), "ak": BAIDU_AK
        }, timeout=REQUEST_TIMEOUT)
        d = r.json()
        if d.get("status") == 0:
            return d.get("results", [])[:limit]
    except Exception as e:
        print(f"[baidu_place]{_safe_error_text(e)}")
    return []

def _parse_lat_lng(text: str) -> Optional[dict]:
    s = str(text or "")
    patterns = [
        r"纬度\s*([+-]?\d+(?:\.\d+)?)[,，\s;；]*经度\s*([+-]?\d+(?:\.\d+)?)",
        r"lat(?:itude)?[:=：]?\s*([+-]?\d+(?:\.\d+)?).*?(?:lng|lon|longitude)[:=：]?\s*([+-]?\d+(?:\.\d+)?)",
        r"([+-]?\d+(?:\.\d+)?)[,，]\s*([+-]?\d+(?:\.\d+)?)",
    ]
    for p in patterns:
        m = re.search(p, s, flags=re.I)
        if m:
            lat, lng = float(m.group(1)), float(m.group(2))
            if -90 <= lat <= 90 and -180 <= lng <= 180:
                return {"lat": lat, "lng": lng}
    return None

def _coerce_float(value):
    if value is None or value == "":
        return None
    try:
        return float(str(value).strip())
    except (TypeError, ValueError):
        return None

def _extract_coord_pair(value) -> Optional[dict]:
    if isinstance(value, dict):
        lat = _coerce_float(value.get("lat") or value.get("latitude") or value.get("y"))
        lng = _coerce_float(value.get("lng") or value.get("lon") or value.get("longitude") or value.get("x"))
        if lat is not None and lng is not None and -90 <= lat <= 90 and -180 <= lng <= 180:
            return {"lat": lat, "lng": lng}
    s = str(value or "").strip()
    if not s:
        return None
    m = re.search(r"([+-]?\d+(?:\.\d+)?)[,，]\s*([+-]?\d+(?:\.\d+)?)", s)
    if not m:
        return None
    a, b = float(m.group(1)), float(m.group(2))
    if abs(a) <= 90 and abs(b) <= 180:
        return {"lat": a, "lng": b}
    if abs(b) <= 90 and abs(a) <= 180:
        return {"lat": b, "lng": a}
    return None

def _extract_baidu_path_points(steps: list) -> list:
    points = []
    for step in steps or []:
        path = step.get("path") or ""
        if isinstance(path, str) and path:
            for pair in path.split(";"):
                loc = _extract_coord_pair(pair)
                if loc:
                    points.append(loc)
        for key in ("start_location", "end_location"):
            loc = _extract_coord_pair(step.get(key) or {})
            if loc:
                points.append(loc)
    deduped = []
    for p in points:
        if not deduped or abs(deduped[-1]["lat"] - p["lat"]) > 1e-7 or abs(deduped[-1]["lng"] - p["lng"]) > 1e-7:
            deduped.append(p)
    return deduped

def _attach_item_coords(items: list, city: str = "") -> list:
    out = []
    for item in items or []:
        x = dict(item)
        loc = (
            _extract_coord_pair(x)
            or _extract_coord_pair(x.get("location"))
            or _extract_coord_pair(x.get("coordinate"))
            or _extract_coord_pair(x.get("geo"))
        )
        if not loc:
            query = x.get("address") or x.get("name") or ""
            if query:
                loc = geocode_baidu(query, city)
        if loc:
            x["lat"] = loc["lat"]
            x["lng"] = loc["lng"]
        out.append(x)
    return out

def _map_poi(name: str, lat=None, lng=None, category: str = "") -> Optional[dict]:
    lat_f, lng_f = _coerce_float(lat), _coerce_float(lng)
    if lat_f is None or lng_f is None:
        return None
    return {"name": name or category or "地点", "lat": lat_f, "lng": lng_f, "category": category, "label": name or category}

def _build_map_data(center: dict = None, route_points: list = None, poi_groups: list = None) -> dict:
    route_points = [
        {"lat": float(p["lat"]), "lng": float(p["lng"])}
        for p in (route_points or [])
        if p and _coerce_float(p.get("lat")) is not None and _coerce_float(p.get("lng")) is not None
    ]
    pois = []
    for group in poi_groups or []:
        category = group.get("category", "")
        for item in group.get("items", []) or []:
            poi = _map_poi(item.get("name") or item.get("raw") or category, item.get("lat"), item.get("lng"), category)
            if poi:
                pois.append(poi)
    center_poi = _map_poi((center or {}).get("name", ""), (center or {}).get("lat"), (center or {}).get("lng"), "center")
    if center_poi:
        center_data = {"lat": center_poi["lat"], "lng": center_poi["lng"], "name": center_poi["name"]}
    elif pois:
        center_data = {"lat": pois[0]["lat"], "lng": pois[0]["lng"], "name": pois[0]["name"]}
    elif route_points:
        center_data = {"lat": route_points[0]["lat"], "lng": route_points[0]["lng"], "name": "路线起点"}
    else:
        center_data = None
    return {"center": center_data, "routePoints": route_points, "pois": pois}

CITY_GEO_INDEX = {
    "上海": {"name":"上海","lat":31.2304,"lng":121.4737,"country":"中国","province":"上海","airport":"上海虹桥/浦东机场","rail":"上海虹桥站"},
    "北京": {"name":"北京","lat":39.9042,"lng":116.4074,"country":"中国","province":"北京","airport":"北京首都/大兴机场","rail":"北京南站"},
    "杭州": {"name":"杭州","lat":30.2741,"lng":120.1551,"country":"中国","province":"浙江","airport":"杭州萧山机场","rail":"杭州东站"},
    "苏州": {"name":"苏州","lat":31.2989,"lng":120.5853,"country":"中国","province":"江苏","airport":"上海虹桥/无锡硕放机场","rail":"苏州站"},
    "南京": {"name":"南京","lat":32.0603,"lng":118.7969,"country":"中国","province":"江苏","airport":"南京禄口机场","rail":"南京南站"},
    "广州": {"name":"广州","lat":23.1291,"lng":113.2644,"country":"中国","province":"广东","airport":"广州白云机场","rail":"广州南站"},
    "深圳": {"name":"深圳","lat":22.5431,"lng":114.0579,"country":"中国","province":"广东","airport":"深圳宝安机场","rail":"深圳北站"},
    "厦门": {"name":"厦门","lat":24.4798,"lng":118.0894,"country":"中国","province":"福建","airport":"厦门高崎机场","rail":"厦门北站"},
    "漳州": {"name":"漳州","lat":24.5130,"lng":117.6471,"country":"中国","province":"福建","airport":"厦门高崎机场","rail":"漳州站"},
    "桂林": {"name":"桂林","lat":25.2736,"lng":110.2900,"country":"中国","province":"广西","airport":"桂林两江机场","rail":"桂林北站"},
    "成都": {"name":"成都","lat":30.5728,"lng":104.0668,"country":"中国","province":"四川","airport":"成都天府/双流机场","rail":"成都东站"},
    "西安": {"name":"西安","lat":34.3416,"lng":108.9398,"country":"中国","province":"陕西","airport":"西安咸阳机场","rail":"西安北站"},
    "香港": {"name":"香港","lat":22.3193,"lng":114.1694,"country":"中国","province":"香港","airport":"香港国际机场","rail":"香港西九龙站"},
    "澳门": {"name":"澳门","lat":22.1987,"lng":113.5439,"country":"中国","province":"澳门","airport":"澳门国际机场","rail":"珠海站"},
    "新加坡": {"name":"新加坡","lat":1.3521,"lng":103.8198,"country":"新加坡","province":"","airport":"樟宜机场","rail":"市区 MRT"},
    "东京": {"name":"东京","lat":35.6762,"lng":139.6503,"country":"日本","province":"","airport":"羽田/成田机场","rail":"东京站"},
    "大阪": {"name":"大阪","lat":34.6937,"lng":135.5023,"country":"日本","province":"","airport":"关西国际机场","rail":"新大阪站"},
    "首尔": {"name":"首尔","lat":37.5665,"lng":126.9780,"country":"韩国","province":"","airport":"仁川机场","rail":"首尔站"},
    "巴黎": {"name":"巴黎","lat":48.8566,"lng":2.3522,"country":"法国","province":"","airport":"戴高乐机场","rail":"巴黎北站"},
    "伦敦": {"name":"伦敦","lat":51.5072,"lng":-0.1276,"country":"英国","province":"","airport":"希思罗机场","rail":"King's Cross / St Pancras"},
    "纽约": {"name":"纽约","lat":40.7128,"lng":-74.0060,"country":"美国","province":"","airport":"JFK / Newark / LaGuardia","rail":"Penn Station"},
}

CITY_ALIASES = {
    "Singapore": "新加坡", "singapore": "新加坡",
    "Beijing": "北京", "beijing": "北京",
    "Shanghai": "上海", "shanghai": "上海",
    "Hangzhou": "杭州", "hangzhou": "杭州",
    "Suzhou": "苏州", "suzhou": "苏州",
    "Xiamen": "厦门", "xiamen": "厦门",
    "Zhangzhou": "漳州", "zhangzhou": "漳州",
    "Guilin": "桂林", "guilin": "桂林",
    "Tokyo": "东京", "tokyo": "东京",
    "Paris": "巴黎", "paris": "巴黎",
    "London": "伦敦", "london": "伦敦",
    "New York": "纽约", "new york": "纽约",
}

CITY_KEYWORDS = {
    "上海": ["上海", "黄浦", "静安", "徐汇", "浦东", "虹口", "长宁", "普陀", "杨浦", "闵行", "宝山", "嘉定", "青浦", "松江", "奉贤", "金山", "崇明"],
    "杭州": ["杭州", "西湖", "拱墅", "上城", "滨江", "萧山", "余杭", "临平", "钱塘", "富阳", "临安"],
    "北京": ["北京", "朝阳", "海淀", "东城", "西城", "丰台", "石景山", "通州", "昌平", "大兴", "顺义"],
    "深圳": ["深圳", "南山", "福田", "罗湖", "宝安", "龙岗", "龙华", "盐田", "坪山", "光明"],
    "苏州": ["苏州", "姑苏", "工业园区", "吴中", "相城", "虎丘", "吴江", "昆山", "太仓", "常熟", "张家港"],
    "南京": ["南京", "玄武", "秦淮", "建邺", "鼓楼", "浦口", "栖霞", "雨花台", "江宁", "六合"],
    "广州": ["广州", "越秀", "荔湾", "海珠", "天河", "白云", "黄埔", "番禺", "花都", "南沙"],
    "厦门": ["厦门", "思明", "湖里", "集美", "海沧", "同安", "翔安", "鼓浪屿"],
    "漳州": ["漳州", "芗城", "龙文", "龙海", "长泰", "漳浦", "云霄", "东山", "南靖", "平和", "华安"],
    "桂林": ["桂林", "象山", "秀峰", "叠彩", "七星", "雁山", "阳朔", "临桂", "漓江", "东西巷"],
    "成都": ["成都", "锦江", "青羊", "金牛", "武侯", "成华", "高新", "天府新区", "双流", "郫都"],
    "西安": ["西安", "新城", "碑林", "莲湖", "雁塔", "未央", "灞桥", "长安", "曲江"],
    "新加坡": ["Singapore", "新加坡", "Marina", "Orchard", "Bedok", "Geylang", "East Coast", "Changi", "Bugis", "Sentosa"],
}

CITY_CENTER = {
    "上海": (31.2304, 121.4737),
    "杭州": (30.2741, 120.1551),
    "北京": (39.9042, 116.4074),
    "深圳": (22.5431, 114.0579),
    "苏州": (31.2989, 120.5853),
    "南京": (32.0603, 118.7969),
    "广州": (23.1291, 113.2644),
    "厦门": (24.4798, 118.0894),
    "漳州": (24.5130, 117.6471),
    "桂林": (25.2736, 110.2900),
    "成都": (30.5728, 104.0668),
    "西安": (34.3416, 108.9398),
    "新加坡": (1.3521, 103.8198),
}

def _clean_place_token(value: str) -> str:
    s = str(value or "").strip()
    s = re.sub(r"^[我咱咱们我们]*(?:从|在|由|自|去|到|前往|飞往|飞到|出发去)?", "", s)
    s = re.sub(r"(?:预算|人均|总预算|总共|打算|计划|准备|想用|想在|想住|想吃|出差|旅游|旅行|开会|游玩|玩|周末|半日|天气|路线|行程|建议|怎么走|怎么去|规划|安排|告诉我|请|一下|一趟|\d+\s*天).*$", "", s)
    s = re.sub(r"[，。！？、,.!?;；：:\s]+$", "", s)
    return s.strip(" -→")

def _city_alias(name: str) -> str:
    n = _clean_place_token(name)
    if n in CITY_GEO_INDEX:
        return n
    if n in CITY_ALIASES:
        return CITY_ALIASES[n]
    low = n.lower()
    if low in CITY_ALIASES:
        return CITY_ALIASES[low]
    for k in sorted(CITY_GEO_INDEX, key=len, reverse=True):
        if k and k in n:
            return k
    return n

def _guard_city_name(city: str) -> str:
    c = _city_alias((city or "").replace("市", "").strip())
    return c if c in CITY_GEO_INDEX or c in CITY_KEYWORDS else c

def filter_results_by_city(results, city):
    if not city or not isinstance(results, list):
        return results
    city_key = _guard_city_name(city)
    keywords = CITY_KEYWORDS.get(city_key, [city_key])
    filtered = []
    for item in results:
        text = " ".join([
            str(item.get("name", "")),
            str(item.get("address", "")),
            str(item.get("type", "")),
            str(item.get("tag", "")),
            str(item.get("city", "")),
        ])
        if any(k and k in text for k in keywords):
            filtered.append(item)
    return filtered

def _city_guard_block(city: str, result: dict = None) -> dict:
    city_key = _guard_city_name(city)
    source = (result or {}).get("source", "meituan_skill")
    return {
        "success": False,
        "fallback": True,
        "message": f"未找到符合 {city_key} 的真实本地结果，已阻止跨城市错误推荐，请重新搜索。",
        "city_guard": "blocked_cross_city_results",
        "city": city_key,
        "source": source,
        "is_real_meituan": False,
    }

def is_coord_near_city(lat, lng, city, max_km=80):
    city_key = _guard_city_name(city)
    if not lat or not lng or city_key not in CITY_CENTER:
        return True
    city_lat, city_lng = CITY_CENTER[city_key]
    d = _haversine(float(lat), float(lng), city_lat, city_lng)
    return d <= max_km

def _apply_city_guard_to_result(result: dict, city: str) -> dict:
    if not isinstance(result, dict) or not result.get("success"):
        return result
    results = result.get("results")
    if not isinstance(results, list):
        return result
    filtered = filter_results_by_city(results, city)
    if not filtered:
        blocked = _city_guard_block(city, result)
        blocked.update({
            "intent": result.get("intent", ""),
            "keyword": result.get("keyword", ""),
            "detail": result.get("detail", ""),
        })
        return blocked
    guarded = dict(result)
    guarded["results"] = filtered
    guarded["count"] = len(filtered)
    guarded["city"] = _guard_city_name(city) or result.get("city", city)
    guarded["city_guard"] = "passed"
    return guarded

def _extract_origin_destination(prompt: str, city_hint: str = "",
                                origin: str = "", destination: str = "") -> dict:
    s = str(prompt or "")
    start = _clean_place_token(origin)
    dest = _clean_place_token(destination)
    patterns = [
        r"从\s*([^，。！？,;；]{1,30}?)(?:出发)?(?:到|去|至|前往|飞往|飞到|抵达)\s*([^，。！？,;；]{1,30})",
        r"([^，。！？,;；]{1,30}?)(?:→|->|至)\s*([^，。！？,;；]{1,30})",
    ]
    if not (start and dest):
        for p in patterns:
            m = re.search(p, s)
            if m:
                start = start or _clean_place_token(m.group(1))
                dest = dest or _clean_place_token(m.group(2))
                break
    if not dest:
        m = re.search(r"(?:去|前往|到)\s*([^，。！？,;；]{2,20}?)(?:出差|旅游|旅行|开会|游玩|玩|周末|天气|行程|路线|$)", s)
        if m:
            dest = _clean_place_token(m.group(1))
    if not start:
        start = _clean_place_token(city_hint) or "当前位置"
    return {"origin": start or "当前位置", "destination": dest}

def _resolve_place_info(name: str, city_hint: str = "") -> dict:
    raw = _clean_place_token(name) or _clean_place_token(city_hint) or "当前位置"
    key = _city_alias(raw)
    if key in CITY_GEO_INDEX:
        info = dict(CITY_GEO_INDEX[key])
        info["raw"] = raw
        return info
    loc = geocode_openmeteo(key)
    if loc:
        country = loc.get("country") or ""
        info = {
            "name": loc.get("name") or key, "raw": raw,
            "lat": loc.get("lat"), "lng": loc.get("lng"),
            "country": "中国" if country in ("China", "中国") else country,
            "province": "", "airport": f"{loc.get('name') or key}机场",
            "rail": f"{loc.get('name') or key}火车站",
        }
        return info
    b = geocode_baidu(key, city_hint)
    if b:
        return {
            "name": key, "raw": raw, "lat": b["lat"], "lng": b["lng"],
            "country": "中国", "province": "", "airport": f"{key}机场", "rail": f"{key}站",
        }
    return {
        "name": key, "raw": raw, "lat": None, "lng": None,
        "country": "中国", "province": "", "airport": f"{key}机场", "rail": f"{key}站",
    }

def _geo_distance_km(a: dict, b: dict) -> float:
    if not all([a.get("lat"), a.get("lng"), b.get("lat"), b.get("lng")]):
        return 0.0
    return round(_haversine(float(a["lat"]), float(a["lng"]), float(b["lat"]), float(b["lng"])), 1)

def _judge_travel_scope(origin: dict, dest: dict, distance_km: float) -> dict:
    country_a = origin.get("country") or "中国"
    country_b = dest.get("country") or "中国"
    if country_a != country_b:
        return {"scope":"cross_country","label":"跨国出行","priority":"飞机优先","threshold":"跨国"}
    if distance_km > 500:
        return {"scope":"long_distance","label":"跨省/远距离城市","priority":"飞机/高铁优先","threshold":"直线距离 > 500km"}
    if (
        origin.get("name") and dest.get("name")
        and origin.get("name") != dest.get("name")
        and origin.get("province") and origin.get("province") == dest.get("province")
        and distance_km >= 20
    ):
        return {"scope":"regional","label":"同省短途跨城","priority":"高铁/城际优先","threshold":"同省跨城"}
    if distance_km >= 50:
        return {"scope":"regional","label":"中距离跨城","priority":"高铁/自驾优先","threshold":"50-500km"}
    if distance_km >= 5:
        return {"scope":"same_city_cross_area","label":"同市跨片区","priority":"地铁/打车/步行按距离选择","threshold":"5-50km"}
    return {"scope":"short","label":"短途出行","priority":"步行优先","threshold":"<5km"}

def _duration_label(hours: float) -> str:
    if hours < 1:
        return f"约{max(10, round(hours * 60))}分钟"
    return f"约{hours:.1f}小时".replace(".0", "")

def _panorama_map_urls(origin: dict, dest: dict) -> dict:
    o = quote(origin.get("name") or "")
    d = quote(dest.get("name") or "")
    return {
        "baidu": f"https://map.baidu.com/dir/?origin=name:{o}&destination=name:{d}&mode=transit&output=html",
        "gaode": f"https://www.amap.com/dir?from[name]={o}&to[name]={d}&type=bus",
        "google": f"https://www.google.com/maps/dir/{o}/{d}/?travelmode=transit",
        "flight": f"https://www.google.com/travel/flights?q=Flights%20from%20{o}%20to%20{d}",
    }

def _wants_flight_travel(text: str) -> bool:
    return bool(re.search(r"飞机|航班|机票|机场|飞去|飞到|坐飞机|flight|airline|airport", str(text or ""), flags=re.I))

def _wants_bike_transport(text: str) -> bool:
    return bool(re.search(r"骑行|骑车|骑自行车|自行车|共享单车|单车|bike|bicycle|cycling", str(text or ""), flags=re.I))

def _flight_query_info(origin: dict, dest: dict, map_urls: dict,
                       distance_km: float, decision: dict,
                       flight_requested: bool) -> dict:
    enabled = bool(flight_requested or decision.get("scope") in ("cross_country", "long_distance"))
    if not enabled:
        return {"enabled": False}
    reason = "用户明确提到飞机/航班，已优先接入航班查询。"
    if not flight_requested:
        reason = "距离较远，飞机可能更快，已提供航班查询入口。"
    if decision.get("scope") in ("same_city_cross_area", "short", "regional") and flight_requested:
        reason = "已按你的飞机出行需求提供航班查询入口，但当前距离通常更适合地铁/高铁/自驾。"
    return {
        "enabled": True,
        "reason": reason,
        "provider": "Google Flights",
        "origin_airport": origin.get("airport", ""),
        "destination_airport": dest.get("airport", ""),
        "query_url": map_urls.get("flight", ""),
        "distance_km": distance_km,
        "note": "航班班次、票价和余票以打开后的航班查询页面为准。",
    }

def _build_panorama_legs(origin: dict, dest: dict, distance_km: float, decision: dict,
                         flight_requested: bool = False,
                         bike_requested: bool = False) -> tuple[list, list, list]:
    scope = decision["scope"]
    long_legs, local_legs, backup_legs = [], [], []
    if scope == "cross_country":
        fly_h = max(2.0, distance_km / 780 + 1.8)
        long_legs.append({"mode":"飞机","title":"主推荐：国际/跨境航班","duration":_duration_label(fly_h),
                          "route":f"{origin.get('airport')} → {dest.get('airport')}",
                          "reason":"跨国出行必须优先长途交通，步行只做落地短途；骑行需用户明确提出。"})
        long_legs.append({"mode":"高铁/火车","title":"备选：仅在有直达铁路时考虑","duration":"通常不作为首选",
                          "route":f"{origin.get('rail')} → {dest.get('rail')}",
                          "reason":"跨国铁路受签证、班次和换乘影响，适合作为低预算备选。"})
        local_legs.extend([
            {"mode":"地铁","title":"落地后市内接驳","duration":"约45-75分钟","route":f"{dest.get('airport')} → 市区/酒店", "reason":"成本低、稳定，不受打车排队影响。"},
            {"mode":"打车","title":"落地后快速接驳","duration":"约35-60分钟","route":f"{dest.get('airport')} → 目的地", "reason":"行李多或夜间抵达更省心。"},
        ])
    elif scope == "long_distance":
        rail_h = max(3.0, distance_km / 260 + 0.8)
        fly_h = max(2.0, distance_km / 760 + 1.6)
        rail_leg = {"mode":"高铁","title":"主推荐：高铁优先","duration":_duration_label(rail_h), "route":f"{origin.get('rail')} → {dest.get('rail')}", "reason":"市中心到市中心更稳定，适合跨省远距离。"}
        flight_leg = {"mode":"飞机","title":"备选：航班更快","duration":_duration_label(fly_h), "route":f"{origin.get('airport')} → {dest.get('airport')}", "reason":"距离很长或高铁票紧张时优先。"}
        if flight_requested or fly_h + 0.4 < rail_h:
            flight_leg["title"] = "主推荐：航班查询"
            flight_leg["reason"] = "飞机总耗时更有优势，或用户明确偏好飞机出行。"
            rail_leg["title"] = "备选：高铁稳定"
            long_legs.extend([flight_leg, rail_leg])
        else:
            long_legs.extend([rail_leg, flight_leg])
        local_legs.extend([
            {"mode":"地铁","title":"到站后接驳","duration":"约25-50分钟","route":f"{dest.get('rail')} / {dest.get('airport')} → 目的地", "reason":"稳定、成本低。"},
            {"mode":"打车","title":"到站后快速接驳","duration":"约20-45分钟","route":"交通枢纽 → 酒店/会场", "reason":"赶时间、携带行李时更合适。"},
        ])
    elif scope == "regional":
        drive_h = max(1.0, distance_km / 85)
        rail_h = max(0.7, distance_km / 230 + 0.4)
        long_legs.extend([
            {"mode":"高铁","title":"主推荐：城际高铁","duration":_duration_label(rail_h), "route":f"{origin.get('rail')} → {dest.get('rail')}", "reason":"50-500km 区间效率高，适合周末/出差。"},
            {"mode":"自驾","title":"备选：自驾直达","duration":_duration_label(drive_h), "route":f"{origin.get('name')} → {dest.get('name')}", "reason":"同行多人或目的地分散时更自由。"},
        ])
        local_legs.append({"mode":"地铁/打车","title":"到达后接驳","duration":"约15-40分钟","route":f"{dest.get('rail')} → 目的地", "reason":"按行李和时间选择。"})
    elif scope == "same_city_cross_area":
        if bike_requested:
            local_legs.append({"mode":"骑行","title":"按你要求：骑行路线","duration":_duration_label(max(0.25, distance_km / 14)), "route":f"{origin.get('name')} → {dest.get('name')}", "reason":"用户明确提出骑行，优先规划路况友好路段。"})
        local_legs.extend([
            {"mode":"地铁","title":"主推荐：同城跨片区","duration":_duration_label(max(0.3, distance_km / 35)), "route":f"{origin.get('name')} → {dest.get('name')}", "reason":"城市内默认优先地铁，稳定且成本可控。"},
            {"mode":"打车","title":"备选：更省步行","duration":_duration_label(max(0.25, distance_km / 30)), "route":f"{origin.get('name')} → {dest.get('name')}", "reason":"赶时间、天气不好或同行多人时合适。"},
            {"mode":"步行","title":"末段接驳","duration":"约5-20分钟","route":"地铁站/下车点 → 目的地", "reason":"用于景区、街区内部移动。"},
        ])
    else:
        if bike_requested:
            local_legs.append({"mode":"短途骑行","title":"按你要求：共享单车","duration":_duration_label(max(0.08, distance_km / 12)), "route":"避开机动车密集路段", "reason":"用户明确提出骑行，作为短距离主方案。"})
        local_legs.append({"mode":"步行","title":"主推荐：步行","duration":_duration_label(max(0.1, distance_km / 4.5)), "route":f"{origin.get('name')} → {dest.get('name')}", "reason":"<5km 默认步行，低成本且稳定。"})
    backup_legs.extend([
        {"mode":"步行","title":"最后一公里备选","duration":"约5-15分钟","route":"地铁/停车点 → 目的地", "reason":"用于落地短驳，不替代长途交通。"},
    ])
    if bike_requested:
        backup_legs.append({"mode":"短途骑行","title":"短距离补充","duration":"约5-20分钟","route":"同街区/同园区内移动", "reason":"仅因用户明确提出骑行，且只在安全路段启用。"})
    return long_legs, local_legs, backup_legs

def _weather_aux(city_name: str) -> dict:
    r = tool_get_weather(city_name)
    if not r.get("success"):
        return {"available": False, "text": "天气暂不可用，仅作为辅助信息。"}
    d = r.get("data", {})
    return {
        "available": True, "city": r.get("city", city_name),
        "text": d.get("text", ""), "temp": d.get("temp", ""),
        "feels_like": d.get("feels_like", ""), "wind": f"{d.get('wind_dir','')}{d.get('wind_class','')}",
        "rh": d.get("rh", ""), "note": "天气只影响接驳和装备建议，不覆盖主交通判断。",
    }

def tool_plan_panorama_trip(city: str, user_prompt: str,
                            origin: str = "", destination: str = "",
                            persona: str = "", map_provider: str = "") -> dict:
    od = _extract_origin_destination(user_prompt, city, origin, destination)
    if not od.get("destination"):
        return {"success": False, "error": "没有识别到目标目的地，请补充要去哪里。"}
    start = _resolve_place_info(od["origin"], city)
    dest = _resolve_place_info(od["destination"], city)
    distance_km = _geo_distance_km(start, dest)
    decision = _judge_travel_scope(start, dest, distance_km)
    flight_requested = _wants_flight_travel(user_prompt)
    bike_requested = _wants_bike_transport(user_prompt)
    if flight_requested:
        decision = dict(decision)
        decision["flight_query"] = True
        if decision.get("scope") in ("cross_country", "long_distance"):
            decision["priority"] = "飞机/航班查询优先"
    if bike_requested and decision.get("scope") in ("same_city_cross_area", "short"):
        decision = dict(decision)
        decision["priority"] = "按用户要求优先骑行，地铁/打车/步行保留备选"
    long_legs, local_legs, backup_legs = _build_panorama_legs(start, dest, distance_km, decision, flight_requested, bike_requested)
    provider = _detect_map_provider(user_prompt, map_provider or "gaode")
    map_urls = _panorama_map_urls(start, dest)
    flight_query = _flight_query_info(start, dest, map_urls, distance_km, decision, flight_requested)
    status_flow = [
        f"正在识别出发地：{start.get('name')}，目的地：{dest.get('name')}",
        f"正在判定地域层级：{decision['label']}",
        f"正在按 {decision['threshold']} 选择交通方式",
        "已接入航班查询入口" if flight_query.get("enabled") else "无需航班查询，优先本地/铁路交通",
        "全景行程已生成：长途交通 + 市内接驳",
    ]
    title = f"{start.get('name')} → {dest.get('name')} 全景行程"
    summary = f"{decision['label']}，直线约 {distance_km or '-'} km，{decision['priority']}。天气仅作辅助，不抢占主交通方案。"
    return {
        "success": True, "type": "panorama_trip",
        "title": title, "summary": summary,
        "city": city, "origin": start, "destination": dest,
        "distance_km": distance_km, "decision": decision,
        "persona": persona or "", "persona_label": PERSONA_LABELS.get((persona or "").strip().lower(), ""),
        "map_provider": provider, "map_urls": map_urls,
        "flight_query": flight_query,
        "status_flow": status_flow,
        "long_distance": long_legs,
        "local_transfer": local_legs,
        "short_backup": backup_legs,
        "weather": _weather_aux(dest.get("name") or city),
        "data_layer": {
            "geo": "known_city_or_geocode",
            "distance": "haversine",
            "transport_decision": "rule_engine",
            "weather": "open_meteo_auxiliary",
        },
        "fixed_rule": "路线/跨城出行优先，天气只做辅助；用户未明确骑行时不默认骑行。",
    }

def _looks_panorama_trip(text: str) -> bool:
    s = str(text or "")
    if re.search(r"跨国|跨省|跨城|出差|高铁|飞机|机场|航班|火车|落地|接驳|长途|城际|自驾", s):
        return True
    mentioned = [c for c in CITY_GEO_INDEX if c in s]
    if len(set(mentioned)) >= 2 and re.search(r"从|到|去|至|前往|→|->", s):
        return True
    return bool(re.search(r"从.+?(?:到|去|至|前往).+?(?:怎么走|路线|行程|出行|交通|建议)", s))

ZH_NUM_MAP = {"一":1, "二":2, "两":2, "三":3, "四":4, "五":5, "六":6, "七":7, "八":8, "九":9, "十":10}

def _zh_to_int(value: str, default: int = 0) -> int:
    s = str(value or "").strip()
    if not s:
        return default
    if s.isdigit():
        return int(s)
    if s in ZH_NUM_MAP:
        return ZH_NUM_MAP[s]
    if "十" in s:
        left, _, right = s.partition("十")
        return (ZH_NUM_MAP.get(left, 1) * 10) + ZH_NUM_MAP.get(right, 0)
    return default

def _is_valid_place_name(name: str) -> bool:
    """粗略判断提取出的地名是否像真实地点，而非用户话术片段。"""
    if not name or len(name) < 2:
        return False
    # 已知城市直接通过
    if _city_alias(name) in CITY_GEO_INDEX:
        return True
    # 包含明显话术词则拒绝
    reject_words = ("帮我", "给我", "做个", "做一个", "规划", "攻略", "安排", "出游",
                    "一天", "两天", "三天", "一日", "两日", "周末", "旅游", "旅行",
                    "怎么", "如何", "建议", "推荐", "什么", "哪里", "一下")
    return not any(w in name for w in reject_words)

def _extract_trip_points(text: str, city_hint: str = "") -> dict:
    s = str(text or "")
    origin = ""
    destination = ""
    patterns = [
        r"从\s*([^#，。！？,;；\s]{2,12})\s*(?:出发)?(?:去|到|前往)\s*([^#，。！？,;；\s]{2,12})(?:[#，。！？,;；]|玩|旅游|旅行|周末游|游玩|待|行程|规划|$)",
        r"我在\s*([^#，。！？,;；\s]{2,12}).*?(?:想|要|打算)?(?:去|到|前往)\s*([^#，。！？,;；\s]{2,12})(?:[#，。！？,;；]|玩|旅游|旅行|周末游|游玩|待|行程|规划|$)",
        r"(?:想去|打算去|准备去|计划去|要去|去|到|前往)\s*([^#，。！？,;；\s]{2,12})(?:[#，。！？,;；]|玩|旅游|旅行|周末游|游玩|待|行程|规划|$)",
        r"([^#，。！？,;；\s]{2,12})(?:玩|旅游|旅行|周末游)",
    ]
    for p in patterns:
        m = re.search(p, s)
        if not m:
            continue
        if len(m.groups()) == 2:
            o = _clean_place_token(m.group(1))
            d = _clean_place_token(m.group(2))
            if _is_valid_place_name(d):
                origin = o
                destination = d
                break
        else:
            d = _clean_place_token(m.group(1))
            if _is_valid_place_name(d):
                destination = d
                break
    # 城市名直接扫描（最可靠，不依赖正则捕获组）
    if not destination:
        for city in sorted(CITY_GEO_INDEX, key=len, reverse=True):
            if city in s and city != _city_alias(city_hint):
                destination = city
                break
    # 若 city_hint 本身就是目的地，不要置空
    if not destination and city_hint:
        ch = _city_alias(_clean_place_token(city_hint))
        if ch in CITY_GEO_INDEX and ch in s:
            destination = ch
    return {"origin": origin or _clean_place_token(city_hint) or "当前位置", "destination": destination}

def _extract_trip_requirements(prompt: str, city_hint: str = "") -> dict:
    s = str(prompt or "")
    soul_profile = _load_soul_user_profile()
    soul_prefs = soul_profile.get("stable_preferences", {})
    avoid_meituan = bool(re.search(r"不想在美团|不要美团|不用美团|不喜欢美团|讨厌美团|厌恶美团|美团恶心|恶心美团|讨厌的美团|恶心的美团|不在美团下单|不想用美团|不想.*美团|美团.*不(?:下单|订|点)", s))
    avoid_delivery = bool(re.search(r"外卖不想在美团点|不想点外卖|不点外卖|不想.*点外卖|不要外卖", s))
    avoid_hotel_booking = bool(re.search(r"酒店不想在美团订|不想订酒店|不订酒店|不想.*订酒店|不要.*订酒店|不在美团.*订酒店", s))
    plan_only = bool(re.search(r"只要规划|只做规划|只帮我安排路线|只安排路线|只做行程|不(?:要|用).*下单", s))
    wants_meituan = bool(re.search(r"结合美团|美团上|推荐美团|美团券|找团购|团购|找券|美团酒店|美团订酒店|美团下单|点外卖|买团购|真实店名|美团.*(?:推荐|有什么|找|看看|订|下单)", s)) and not avoid_meituan
    requires_real_meituan = bool(re.search(r"真实(?:的)?(?:美团)?(?:店名|酒店|商家)|美团上真实|真实美团|美团.*真实", s)) and not avoid_meituan
    intent = "meituan_trip_plan" if (wants_meituan or requires_real_meituan) else "trip_plan_only"
    if avoid_meituan:
        intent = "no_meituan"
    elif avoid_delivery or avoid_hotel_booking or plan_only:
        intent = "trip_plan_only"
    if avoid_meituan and not re.search(r"行程|规划|路线|攻略|玩|旅游|旅行|游玩", s):
        intent = "no_meituan"
    commerce_mode = "none" if intent in ("trip_plan_only", "no_meituan") else "recommend"
    planner_mode = "independent_trip" if commerce_mode == "none" else "meituan_commerce"
    cta = {"type": "none", "text": ""} if commerce_mode == "none" else {"type": "copy_keywords", "text": "复制推荐关键词"}
    points = _extract_trip_points(s, city_hint)
    dest = points["destination"]
    if not dest:
        m = re.search(r"(?:去|到|前往)\s*([^#，。！？,;；\s]{2,12})(?:玩|旅游|旅行|游玩|行程|攻略|$)", s)
        if m:
            dest = _clean_place_token(m.group(1))
    days = 1
    m_days = re.search(r"([0-9一二两三四五六七八九十]{1,3})\s*天", s)
    if m_days:
        days = max(1, min(10, _zh_to_int(m_days.group(1), 1)))
    budget = 0
    m_budget = re.search(r"(?:预算|人均|总共|总预算)\s*([0-9]+(?:\.[0-9]+)?\s*万|[一二两三四五六七八九十]+\s*万|[0-9]{2,7})", s)
    if not m_budget:
        m_budget = re.search(r"([0-9]+(?:\.[0-9]+)?\s*万|[一二两三四五六七八九十]+\s*万|[0-9]{2,7})\s*(?:元|块|rmb|RMB|以内|以下)", s)
    if m_budget:
        budget = _parse_soul_money(m_budget.group(1))
    if budget <= 0:
        budget = max(800, days * 700)
        soul_budget = soul_prefs.get("budget", {})
        soul_cap = _optional_int(soul_budget.get("default_max_total"), 0) or 0
        if soul_cap:
            budget = min(budget, soul_cap)
    od = _extract_origin_destination(s, city_hint, points["origin"], dest)
    # 要求9：只有用户明确提到出发地才使用，否则用"当前城市"，不硬写前端默认值
    _explicit_origin = points["origin"] or od.get("origin", "")
    _origin_is_default = not _explicit_origin  # 用户未明确说出发地
    origin = _explicit_origin or "当前城市"
    return {
        "origin": origin,
        "origin_is_default": _origin_is_default,
        "destination": dest or od.get("destination") or _clean_place_token(city_hint) or "本地",
        "days": days,
        "budget": budget,
        "wants_meituan": wants_meituan,
        "requires_real_meituan": requires_real_meituan,
        "wants_hotel": bool(re.search(r"酒店|住宿|宾馆|民宿|住哪", s)),
        "intent": intent,
        "commerce_mode": commerce_mode,
        "planner_mode": planner_mode,
        "user_preference": {
            "avoid_meituan": avoid_meituan,
            "avoid_delivery": avoid_delivery,
            "avoid_hotel_booking": avoid_hotel_booking,
        },
        "cta": cta,
        "soul_memory": {
            "summary": _soul_memory_summary(soul_profile),
            "preferences": soul_prefs,
        },
        "raw": s,
    }

def _has_explicit_trip_days(text: str) -> bool:
    return bool(re.search(r"[0-9一二两三四五六七八九十]{1,3}\s*天|周末|半日|一日|当天|当日", str(text or "")))

def _has_explicit_trip_budget(text: str) -> bool:
    s = str(text or "")
    return bool(re.search(r"(?:预算|人均|总共|总预算)\s*(?:[0-9]+(?:\.[0-9]+)?\s*万|[一二两三四五六七八九十]+\s*万|[0-9]{2,7})|(?:[0-9]+(?:\.[0-9]+)?\s*万|[一二两三四五六七八九十]+\s*万|[0-9]{2,7})\s*(?:元|块|rmb|RMB|以内|以下)", s))

def _has_explicit_trip_transport(text: str) -> bool:
    return bool(re.search(r"飞机|航班|机票|机场|高铁|火车|动车|城际|自驾|开车|打车|叫车|地铁|公交|骑行|步行", str(text or ""), flags=re.I))

def _has_explicit_trip_persona(text: str) -> bool:
    return bool(re.search(r"松弛|慢节奏|特种兵|高效|社恐|安静|家庭|亲子|老人|孩子|学生|穷游|拍照|出片|美食|吃货|情侣|浪漫", str(text or "")))

def _transport_default_label(decision: dict) -> str:
    priority = str((decision or {}).get("priority", ""))
    if "飞机" in priority:
        return "飞机优先"
    if "高铁" in priority or "城际" in priority:
        return "高铁优先"
    if "地铁" in priority:
        return "地铁/打车/步行按距离选择"
    if "步行" in priority:
        return "步行优先"
    return priority or "按距离自动选择交通"

def _proactive_butler_defaults(req: dict, decision: dict, persona_state: dict,
                               prompt: str, destination: str = "") -> dict:
    text = str(prompt or "")
    dest = destination or req.get("destination") or "目的地"
    scope = (decision or {}).get("scope", "")
    day_unit = "短途游" if scope in ("regional", "same_city_cross_area", "short") else "出行"
    intro = f"🍊 我先按{req.get('days', 1)}日{day_unit}为你生成方案，不打断你。"
    assumptions = []
    if not _has_explicit_trip_transport(text):
        assumptions.append(_transport_default_label(decision))
    if not _has_explicit_trip_persona(text):
        labels = persona_state.get("labels") or []
        assumptions.append((labels[0] if labels else "松弛感").replace("状态", ""))
    if not _has_explicit_trip_budget(text):
        assumptions.append("预算中等")
    if not assumptions:
        assumptions.append("先出可执行草案")
    workflow = [
        "正在查交通",
        f"正在搜索{dest}景点",
        "正在匹配餐饮",
        "正在生成路线",
    ]
    return {
        "enabled": True,
        "intro": intro,
        "assumptions": assumptions,
        "workflow": workflow,
        "confirmation_policy": "路线、初版行程和预算拆分先主动完成；下单、付款、预约、叫车前再请你确认。",
    }

def _looks_meituan_trip(text: str) -> bool:
    s = str(text or "")
    if not s or re.fullmatch(r".{0,12}(天气|气温|几度|下雨|晴|阴|温度).{0,8}", s):
        return False
    core = re.search(r"行程|攻略|预算|酒店|住宿|宾馆|民宿|美团|景点|门票|[0-9一二两三四五六七八九十]{1,3}\s*天|去.+玩|旅游|旅行|游玩", s)
    return bool(core and re.search(r"去|到|前往|玩|行程|规划|安排|预算|酒店|住宿|美团|景点", s))

def _looks_direct_meituan_resource(text: str) -> bool:
    s = str(text or "")
    if re.search(r"不想在美团|不要美团|不用美团|不想用美团|不在美团", s):
        return False
    if re.search(r"行程|规划|攻略|[0-9一二两三四五六七八九十]{1,3}\s*天|旅游|旅行|游玩|去.+玩", s):
        return False
    has_resource = re.search(r"酒店|住宿|宾馆|民宿|餐厅|美食|外卖|团购|券|优惠|跑腿|帮送|真实店名|商家", s)
    has_meituan = re.search(r"美团|真实|附近|最近|离我|周边", s)
    return bool(has_resource and (has_meituan or _looks_order_draft_request(s)))

def _looks_order_draft_request(text: str) -> bool:
    s = str(text or "")
    if re.search(r"不想在美团|不要美团|不用美团|不想用美团|不在美团|不下单|不要下单", s):
        return False
    return bool(re.search(r"帮我订|帮我预订|代我下单|帮我下单|帮我买票|帮我点外卖|确认下单|确认预订|就这个|下单|预订", s))

def _extract_order_id(text: str) -> str:
    m = re.search(r"MDCG-[A-Z0-9]{8}", str(text or ""), flags=re.I)
    return m.group(0).upper() if m else ""

def _looks_mock_resource_task(text: str) -> bool:
    s = str(text or "")
    return bool(re.search(r"打车|叫车|网约车|出租车|接驳|机票|航班|飞机票|订机票|买机票|排队|等位|有位|满座|监控|提醒我|后台盯|人多", s))

def _mock_resource_final_text(results: list) -> str:
    lines = ["🍊 已启动资源编排："]
    for item in results:
        tool = item.get("tool")
        result = item.get("result", {})
        if tool == "mock_start_service_monitor":
            mon = result.get("monitor", {})
            latest = mon.get("latest", {})
            lines.append(f"- 后台监控：{mon.get('target_name','目标资源')}，{latest.get('message','已开始监控')}，建议：{latest.get('recommended_action','继续观察')}")
        elif tool == "mock_request_ride":
            q = result.get("quote", {})
            oid = result.get("order", {}).get("order_id", "")
            lines.append(f"- 打车待确认：{q.get('origin','')} → {q.get('destination','')}，约{q.get('eta_minutes','-')}分钟到达，预估¥{q.get('price_estimate','-')}，订单 {oid}")
        elif tool == "mock_search_flights":
            rec = result.get("recommended", {})
            oid = result.get("order", {}).get("order_id", "")
            lines.append(f"- 机票待确认：{rec.get('airline','')} {rec.get('flight_id','')}，{rec.get('depart_time','')}起飞，¥{rec.get('price','-')}，订单 {oid}")
    lines.append("所有订单均为待确认状态，只有你点击确认后才会进入模拟下单。🍊")
    return "\n".join(lines)

def _rule_mock_resource_agent_response(user_message: str, city_hint: str = "上海",
                                       persona: str = "", map_provider: str = "") -> Response:
    def generate():
        req = _extract_trip_requirements(user_message, city_hint)
        city = req.get("destination") if req.get("destination") != "本地" else city_hint
        origin = req.get("origin") or city_hint or "当前位置"
        destination = req.get("destination") or city or "目的地"
        results = []
        idx = 1
        if re.search(r"排队|等位|有位|满座|监控|提醒我|后台盯|人多", user_message):
            args = {
                "resource_type": "queue",
                "target_name": destination if destination and destination != "本地" else "目标餐厅/拍照点",
                "city": city,
                "condition": user_message,
                "callback_action": "有位或低排队时提醒；需要时建议叫车",
                "duration_minutes": 30,
                "user_context": {"persona": persona, "budget": req.get("budget"), "city": city},
            }
            yield f"data: {json.dumps({'type':'step_start','id':idx,'tool':'mock_start_service_monitor','input':args}, ensure_ascii=False)}\n\n"
            tr = tool_mock_start_service_monitor(**args)
            yield f"data: {json.dumps({'type':'step_done','id':idx,'tool':'mock_start_service_monitor','result':tr,'summary':_tool_summary('mock_start_service_monitor', args, tr)}, ensure_ascii=False)}\n\n"
            results.append({"tool": "mock_start_service_monitor", "result": tr})
            idx += 1
        if re.search(r"机票|航班|飞机票|订机票|买机票", user_message):
            od = _extract_origin_destination(user_message, city_hint, origin, destination)
            args = {
                "origin": od.get("origin") or origin,
                "destination": od.get("destination") or destination,
                "date": "",
                "budget": req.get("budget", 0),
                "passengers": 1,
                "cabin": "economy",
                "user_context": {"persona": persona, "budget": req.get("budget"), "city": city},
            }
            yield f"data: {json.dumps({'type':'step_start','id':idx,'tool':'mock_search_flights','input':args}, ensure_ascii=False)}\n\n"
            tr = tool_mock_search_flights(**args)
            yield f"data: {json.dumps({'type':'step_done','id':idx,'tool':'mock_search_flights','result':tr,'summary':_tool_summary('mock_search_flights', args, tr)}, ensure_ascii=False)}\n\n"
            results.append({"tool": "mock_search_flights", "result": tr})
            idx += 1
        if re.search(r"打车|叫车|网约车|出租车|接驳", user_message):
            args = {
                "origin": origin,
                "destination": destination if destination != "本地" else "目的地",
                "city": city,
                "trigger_reason": user_message,
                "user_context": {"persona": persona, "budget": req.get("budget"), "city": city},
            }
            yield f"data: {json.dumps({'type':'step_start','id':idx,'tool':'mock_request_ride','input':args}, ensure_ascii=False)}\n\n"
            tr = tool_mock_request_ride(**args)
            yield f"data: {json.dumps({'type':'step_done','id':idx,'tool':'mock_request_ride','result':tr,'summary':_tool_summary('mock_request_ride', args, tr)}, ensure_ascii=False)}\n\n"
            results.append({"tool": "mock_request_ride", "result": tr})
            idx += 1
        yield f"data: {json.dumps({'type':'final','text':_mock_resource_final_text(results)}, ensure_ascii=False)}\n\n"
    return Response(stream_with_context(generate()), mimetype="text/event-stream",
                    headers={"Cache-Control":"no-cache","X-Accel-Buffering":"no"})

def _nearest_city_from_coords(lat: float, lng: float, fallback: str = "") -> str:
    best_city = ""
    best_dist = 999999.0
    for city, info in CITY_GEO_INDEX.items():
        if info.get("lat") is None or info.get("lng") is None:
            continue
        dist = _haversine(float(lat), float(lng), float(info["lat"]), float(info["lng"]))
        if dist < best_dist:
            best_dist = dist
            best_city = city
    return best_city if best_city and best_dist <= 120 else (fallback or best_city)

def _extract_price_high(text: str) -> Optional[int]:
    s = str(text or "")
    m = re.search(r"([0-9]{2,6})\s*(?:元|块|rmb|RMB)?\s*(?:以下|以内|以内的|内|以下的|封顶|以下/晚|以内/晚)", s)
    if not m:
        m = re.search(r"(?:不超过|低于|小于|少于|预算|一晚|每晚|晚上)\s*([0-9]{2,6})", s)
    return int(m.group(1)) if m else None

def _direct_meituan_skill_input(text: str, city_hint: str = "") -> dict:
    s = str(text or "")
    req = _extract_trip_requirements(s, city_hint)
    coords = _parse_lat_lng(s)
    nearby_with_coords = bool(coords and re.search(r"附近|最近|离我|周边", s))
    if re.search(r"跑腿|帮送|帮买|取快递|同城配送|送东西|寄文件|送合同", s):
        intent, keyword = "nearby_search", "美团跑腿"
    elif re.search(r"领券|领红包|优惠券|美团券|红包|羊毛|福利|大额券|神券|隐藏券", s):
        intent, keyword = "group_buy_query", "领美团券"
    elif re.search(r"酒店|住宿|宾馆|民宿", s):
        intent, keyword = "hotel_search", "附近酒店" if nearby_with_coords else "酒店"
    elif re.search(r"外卖|点餐|送餐", s):
        intent, keyword = "nearby_search", "附近外卖"
    elif re.search(r"团购|代金券", s):
        intent, keyword = "group_buy_query", "餐饮团购"
    else:
        intent, keyword = "restaurant_search", "附近美食" if nearby_with_coords else "餐厅"
    filters = {}
    price_high = _extract_price_high(s)
    if price_high:
        filters["price_high"] = price_high
    if nearby_with_coords:
        filters.update({"sort_by": "distance", "distance_radius": 5000})
    city = req.get("destination") or city_hint
    if coords:
        city = _nearest_city_from_coords(coords["lat"], coords["lng"], city)
        if (CITY_GEO_INDEX.get(city) or {}).get("country") not in ("中国",):
            filters.pop("sort_by", None)
            filters.pop("distance_radius", None)
            if intent == "hotel_search":
                keyword = "酒店"
    return {
        "intent": intent,
        "city": city,
        "keyword": keyword,
        "location": "当前位置" if coords else "",
        "user_lat": coords.get("lat") if coords else None,
        "user_lng": coords.get("lng") if coords else None,
        "filters": filters,
        "limit": 5,
    }

def _independent_items(intent: str, city: str = "", keyword: str = "",
                       filters: dict = None, limit: int = 5) -> list:
    # 禁止把用户原话当城市名：只用已知城市或"目的地"兜底
    raw_c = (city or "").replace("市", "").strip()
    c = raw_c if (_city_alias(raw_c) in CITY_GEO_INDEX or
                  any(raw_c in keys for keys in CITY_KEYWORDS.values())) else "目的地"
    if intent == "hotel_search":
        return []
    if intent in ("ticket_search", "group_buy_query"):
        city_routes = {
            "杭州": ["西湖湖滨慢行路线", "灵隐寺/茶田周边区域", "河坊街/南宋御街区域"],
            "上海": ["外滩滨江慢行路线", "武康路/安福路街区", "陆家嘴夜景区域"],
            "北京": ["什刹海胡同慢行路线", "故宫/景山周边区域", "鼓楼/南锣区域"],
            "厦门": ["环岛路海边慢行路线", "鼓浪屿核心游览区域", "沙坡尾/双子塔夜景区域"],
            "桂林": ["象山景区/两江四湖区域", "东西巷/逍遥楼片区", "漓江滨水夜游区域"],
            "苏州": ["拙政园/苏博周边区域", "平江路老城慢行路线", "七里山塘夜游区域"],
        }
        names = city_routes.get(c, [f"{c}代表性景区区域", f"{c}历史文化街区", f"{c}夜游/滨水区域"])
        items = [
            {"name": names[0], "address": f"{c}市区", "rating": "", "cost": "", "distance": "按当天路线选择", "type": "区域景点建议", "booking_status": "自行安排", "advantage": "区域建议，不代表具体商户或门票商品。"},
            {"name": names[1], "address": f"{c}老城/核心商圈", "rating": "", "cost": "", "distance": "按住宿位置调整", "type": "区域景点建议", "booking_status": "自行安排", "advantage": "区域建议，不代表具体商户或门票商品。"},
            {"name": names[2], "address": f"{c}夜游片区", "rating": "", "cost": "", "distance": "晚间安排", "type": "区域景点建议", "booking_status": "自行安排", "advantage": "区域建议，不代表具体商户或门票商品。"},
        ]
    else:
        city_foods = {
            "杭州": ["湖滨商圈餐饮区域", "吴山/河坊街小吃区域", "西湖周边茶馆区域"],
            "上海": ["南京东路/外滩餐饮区域", "老城厢本帮菜区域", "武康路咖啡轻食区域"],
            "北京": ["鼓楼/什刹海餐饮区域", "前门小吃区域", "三里屯轻食区域"],
            "厦门": ["中山路小吃区域", "沙坡尾餐饮区域", "环岛路海鲜区域"],
            "桂林": ["东西巷餐饮区域", "正阳步行街小吃区域", "两江四湖夜宵区域"],
            "苏州": ["平江路餐饮区域", "观前街小吃区域", "山塘街夜宵区域"],
        }
        names = city_foods.get(c, [f"{c}核心商圈餐饮区域", f"{c}小吃/早餐集中区域", f"{c}夜宵/轻食区域"])
        items = [
            {"name": names[0], "address": f"{c}核心商圈/老城片区", "rating": "", "cost": "", "distance": "顺路选择", "type": "餐饮区域建议", "booking_status": "自行安排", "advantage": "区域建议，不代表具体商户。"},
            {"name": names[1], "address": f"{c}居民区或老街附近", "rating": "", "cost": "", "distance": "靠近当天起点", "type": "餐饮区域建议", "booking_status": "自行安排", "advantage": "区域建议，不代表具体商户。"},
            {"name": names[2], "address": f"{c}夜游路线附近", "rating": "", "cost": "", "distance": "晚间顺路", "type": "餐饮区域建议", "booking_status": "自行安排", "advantage": "区域建议，不代表具体商户。"},
        ]
    return [dict(x, source="local_reference", is_real_meituan=False, is_area_suggestion=True,
                 data_level="C_MOCK_REGION", can_order=False) for x in items[:limit]]

def _is_real_meituan_item(item: dict) -> bool:
    return bool(isinstance(item, dict) and item.get("source") == "meituan_skill" and item.get("is_real_meituan"))

def _resource_data_tier(hotels: list, foods: list, sights: list) -> dict:
    real_hotels = [x for x in hotels if _is_real_meituan_item(x)]
    real_foods = [x for x in foods if _is_real_meituan_item(x)]
    real_sights = [x for x in sights if _is_real_meituan_item(x)]
    real_count = len(real_hotels) + len(real_foods) + len(real_sights)
    area_count = len([x for x in [*hotels, *foods, *sights] if x.get("is_area_suggestion")])
    if real_hotels and real_foods and real_sights:
        tier = "A"
        label = "真实资源规划"
    elif real_count:
        tier = "B"
        label = "半真实规划"
    else:
        tier = "C"
        label = "兜底规划"
    return {
        "tier": tier,
        "label": label,
        "use_real_results": bool(real_count),
        "use_fallback_template": not bool(real_count),
        "real_counts": {"hotels": len(real_hotels), "foods": len(real_foods), "sights": len(real_sights)},
        "area_suggestion_count": area_count,
    }

MEITUAN_SKILL_UNAVAILABLE = "美团 Skill 暂不可用，请检查 meituan_skill_tool.json 或 Skill 服务状态"

def _hermes_skill_status() -> dict:
    skill_path = HERMES_SKILL_PATH if os.path.exists(HERMES_SKILL_PATH) else HERMES_PROJECT_SKILL_PATH
    return {
        "enabled": os.path.exists(skill_path),
        "skill_name": HERMES_SKILL_NAME,
        "skill_path": skill_path,
        "project_skill_path": HERMES_PROJECT_SKILL_PATH,
        "role": "planning_decision_learning",
    }

def _order_price(value, default=0) -> int:
    if value is None:
        return default
    m = re.search(r"\d+", str(value))
    return int(m.group(0)) if m else default

def _build_trip_bundle_item(destination: dict, req: dict, budget: dict,
                            hotels: list, foods: list, sights: list) -> dict:
    hotel = hotels[0] if hotels else {}
    restaurant = foods[0] if foods else {}
    activity = sights[0] if sights else {}
    selected = []
    if hotel:
        selected.append({"type": "hotel", "name": hotel.get("name",""), "price": hotel.get("cost",""), "rating": hotel.get("rating",""), "address": hotel.get("address",""), "photo_url": hotel.get("photo_url",""), "source": hotel.get("source",""), "is_real_meituan": hotel.get("is_real_meituan", False)})
    if restaurant:
        selected.append({"type": "restaurant", "name": restaurant.get("name",""), "price": restaurant.get("cost",""), "rating": restaurant.get("rating",""), "address": restaurant.get("address",""), "source": restaurant.get("source",""), "is_real_meituan": restaurant.get("is_real_meituan", False)})
    if activity:
        selected.append({"type": "activity", "name": activity.get("name",""), "price": activity.get("cost",""), "rating": activity.get("rating",""), "address": activity.get("address",""), "source": activity.get("source",""), "is_real_meituan": activity.get("is_real_meituan", False)})
    estimate = (
        _order_price(hotel.get("cost"), budget.get("hotel_nightly_cap", 0)) +
        _order_price(restaurant.get("cost"), max(80, round((budget.get("food", 0) or 0) / max(1, req.get("days", 1))))) +
        _order_price(activity.get("cost"), max(0, round((budget.get("tickets", 0) or 0) / max(1, req.get("days", 1)))))
    )
    return {
        "name": f"{destination.get('name', req.get('destination', '目的地'))}{req.get('days', 1)}天出游资源包",
        "destination": destination.get("name", req.get("destination", "")),
        "days": req.get("days", 1),
        "budget_total": budget.get("total", req.get("budget", 0)),
        "price_estimate": estimate,
        "hotel": hotel,
        "hotel_options": hotels[:3],
        "restaurant": restaurant,
        "activity": activity,
        "selected_items": selected,
        "recommend_reason": "已按预算、评分、距离和当前状态权重筛选，等待你确认后执行模拟下单。",
    }

def _build_resource_order_item(args: dict, result: dict) -> dict:
    items = (result.get("results") or []) if isinstance(result, dict) else []
    top = items[0] if items else {}
    intent = (args or {}).get("intent", "")
    order_kind = {
        "hotel_search": "酒店",
        "restaurant_search": "餐厅",
        "nearby_search": "本地生活",
        "ticket_search": "门票/景点",
        "group_buy_query": "团购",
    }.get(intent, "资源")
    return {
        "name": top.get("name") or f"{(args or {}).get('city','目的地')}{order_kind}",
        "category": order_kind,
        "city": (args or {}).get("city", ""),
        "price_estimate": _order_price(top.get("cost") or top.get("price"), 0),
        "rating": top.get("rating", ""),
        "address": top.get("address", ""),
        "merchant": top,
        "hotel_options": items[:3] if intent == "hotel_search" else [],
        "selected_items": [{
            "type": "hotel" if intent == "hotel_search" else "restaurant" if intent in ("restaurant_search", "nearby_search") else "activity",
            "name": top.get("name", ""),
            "price": top.get("cost") or top.get("price", ""),
            "rating": top.get("rating", ""),
            "address": top.get("address", ""),
            "photo_url": top.get("photo_url", ""),
        }] if top else [],
        "recommend_reason": "已根据预算、位置、评分和当前需求生成订单草稿，等待你确认。",
    }

def _order_validation_tags(item: dict, user_context: dict = None) -> list:
    item = item or {}
    user_context = user_context or {}
    city = _guard_city_name(item.get("city") or item.get("destination") or user_context.get("city") or user_context.get("destination") or "")
    selected = item.get("selected_items") if isinstance(item.get("selected_items"), list) else []
    text = " ".join([
        str(item.get("name", "")),
        str(item.get("city", "")),
        str(item.get("address", "")),
        str(item.get("destination", "")),
        " ".join([str(x.get("address", "")) + " " + str(x.get("name", "")) for x in selected if isinstance(x, dict)]),
    ])
    city_keywords = CITY_KEYWORDS.get(city, [city]) if city else []
    city_ok = True if not city or not text.strip() else any(k and k in text for k in city_keywords)
    budget = _order_price(user_context.get("budget") or item.get("budget_total"), 0)
    price = _order_price(item.get("price_estimate"), 0)
    budget_ok = True if not budget or not price else price <= budget
    distance_ok = bool(item.get("distance") or item.get("distance_km") or item.get("address") or selected)
    rating_raw = str(item.get("rating") or "")
    if not rating_raw and selected:
        rating_raw = str(selected[0].get("rating", ""))
    rating_num = float(re.search(r"\d+(?:\.\d+)?", rating_raw).group(0)) if re.search(r"\d+(?:\.\d+)?", rating_raw) else 0
    rating_ok = True if not rating_num else rating_num >= 4.0
    return [
        {"key": "city", "label": "城市校验", "ok": city_ok},
        {"key": "budget", "label": "预算校验", "ok": budget_ok},
        {"key": "distance", "label": "距离校验", "ok": distance_ok},
        {"key": "rating", "label": "评分校验", "ok": rating_ok},
    ]

def tool_create_pending_order(order_type: str, item: dict, user_context: dict = None) -> dict:
    order_id = "MDCG-" + uuid.uuid4().hex[:8].upper()
    now = int(time.time())
    validation_tags = _order_validation_tags(item or {}, user_context or {})
    order = {
        "order_id": order_id,
        "status": "pending_confirm",
        "order_type": order_type or "unknown",
        "item": item or {},
        "user_context": user_context or {},
        "validation_tags": validation_tags,
        "created_at": now,
        "expire_in_minutes": 15,
        "action_required": "user_confirm",
        "message": "已生成待确认订单，等待用户确认。",
        "cta": {"type": "confirm_mock_order", "text": "确认预订"},
    }
    PENDING_ORDERS[order_id] = order
    return {"success": True, "order": order}

def tool_confirm_mock_order(order_id: str) -> dict:
    order = PENDING_ORDERS.get(order_id)
    if not order:
        return {"success": False, "error": "订单不存在或已过期"}
    order["status"] = "mock_order_success"
    order["confirmed_at"] = int(time.time())
    return {
        "success": True,
        "order_id": order_id,
        "status": "mock_order_success",
        "message": "🍊 模拟下单成功，已加入行程。",
        "order": order,
    }

def _mock_seed(*parts) -> int:
    text = "|".join([str(p or "") for p in parts])
    return sum((idx + 1) * ord(ch) for idx, ch in enumerate(text)) + int(time.time() // 30)

def _mock_int(seed_text: str, low: int, high: int) -> int:
    return random.Random(_mock_seed(seed_text)).randint(low, high)

def _mock_budget_from_context(user_context: dict = None, default: int = 0) -> int:
    ctx = user_context or {}
    for key in ("budget", "budget_total", "total_budget", "max_budget"):
        v = _order_price(ctx.get(key), 0)
        if v:
            return v
    return default

def tool_mock_request_ride(origin: str = "", destination: str = "",
                           city: str = "", trigger_reason: str = "",
                           user_context: dict = None) -> dict:
    """生成打车待确认订单。演示用，不调用真实网约车平台。"""
    ctx = user_context or {}
    origin = origin or ctx.get("origin") or city or "当前位置"
    destination = destination or ctx.get("destination") or city or "目的地"
    seed = f"{city}|{origin}|{destination}|{trigger_reason}"
    eta = _mock_int(seed + "eta", 3, 16)
    distance_km = round(_mock_int(seed + "distance", 18, 86) / 10, 1)
    surge_options = [1.0, 1.0, 1.1, 1.2, 1.4]
    surge = surge_options[_mock_int(seed + "surge", 0, len(surge_options) - 1)]
    price = max(12, round((12 + distance_km * 2.8 + eta * 0.6) * surge))
    driver_count = _mock_int(seed + "drivers", 2, 28)
    dynamic_event = "附近车辆充足，建议现在叫车" if eta <= 8 else "附近运力偏紧，建议提前叫车"
    if surge > 1.2:
        dynamic_event = "当前处于轻微加价，建议保留地铁/步行备选"
    quote = {
        "provider": "马到橙功 Mock Ride",
        "city": city,
        "origin": origin,
        "destination": destination,
        "eta_minutes": eta,
        "distance_km": distance_km,
        "price_estimate": price,
        "surge": surge,
        "driver_count": driver_count,
        "dynamic_event": dynamic_event,
        "trigger_reason": trigger_reason or "用户请求打车/接驳",
    }
    item = {
        "name": f"{origin} → {destination} 打车接驳",
        "city": city,
        "origin": origin,
        "destination": destination,
        "category": "打车",
        "price_estimate": price,
        "distance_km": distance_km,
        "rating": "4.8",
        "selected_items": [{
            "type": "ride_hailing",
            "name": "快车待确认",
            "price": str(price),
            "rating": "4.8",
            "address": f"{origin} → {destination}",
            "eta": f"{eta}分钟",
        }],
        "recommend_reason": dynamic_event,
    }
    pending = tool_create_pending_order("ride_hailing", item, {
        **ctx, "city": city, "origin": origin, "destination": destination,
        "budget": _mock_budget_from_context(ctx, price * 2),
    })
    return {"success": True, "type": "ride_hailing_quote", "quote": quote, "order": pending["order"]}

def tool_mock_search_flights(origin: str = "", destination: str = "",
                             date: str = "", budget: int = 0,
                             passengers: int = 1, cabin: str = "economy",
                             user_context: dict = None) -> dict:
    """生成航班候选和机票待确认订单。演示用，不真实出票。"""
    ctx = user_context or {}
    req = _extract_trip_requirements(f"{origin}到{destination}", origin or ctx.get("origin", "")) if not (origin and destination) else {}
    origin = origin or ctx.get("origin") or req.get("origin") or "出发地"
    destination = destination or ctx.get("destination") or req.get("destination") or "目的地"
    passengers = max(1, int(passengers or ctx.get("passengers") or 1))
    budget = int(budget or _mock_budget_from_context(ctx, 0) or 0)
    seed = f"{origin}|{destination}|{date}|{passengers}|{cabin}"
    base = _mock_int(seed + "price", 420, 1180)
    times = [("08:35", "10:50"), ("13:20", "15:35"), ("19:05", "21:25")]
    airlines = ["橙航 Mock Air", "城市快线", "东海航空模拟"]
    options = []
    for idx, (depart, arrive) in enumerate(times):
        price = max(280, base + idx * _mock_int(seed + str(idx), 70, 160) - (60 if idx == 1 else 0))
        option = {
            "flight_id": f"MFA{_mock_int(seed + 'fid' + str(idx), 1000, 9999)}",
            "airline": airlines[idx],
            "origin": origin,
            "destination": destination,
            "depart_time": depart,
            "arrive_time": arrive,
            "duration": "约2小时15分",
            "price": price,
            "left_seats": _mock_int(seed + "seat" + str(idx), 2, 18),
            "budget_ok": True if not budget else price * passengers <= budget,
            "cabin": "经济舱" if cabin == "economy" else cabin,
            "source": "mock_flight_api",
        }
        options.append(option)
    best = next((x for x in options if x["budget_ok"]), min(options, key=lambda x: x["price"]))
    item = {
        "name": f"{origin} → {destination} 机票",
        "city": destination,
        "origin": origin,
        "destination": destination,
        "category": "机票",
        "price_estimate": best["price"] * passengers,
        "rating": "4.7",
        "flight": best,
        "selected_items": [{
            "type": "flight_ticket",
            "name": f"{best['airline']} {best['flight_id']}",
            "price": f"{best['price']} × {passengers}",
            "rating": "4.7",
            "address": f"{origin} {best['depart_time']} → {destination} {best['arrive_time']}",
        }],
        "recommend_reason": "已按价格、余票、时间和预算匹配最合适航班，等待确认后模拟出票。",
    }
    pending = tool_create_pending_order("flight_ticket", item, {
        **ctx, "city": destination, "origin": origin, "destination": destination,
        "budget": budget or best["price"] * passengers * 2,
        "passengers": passengers,
    })
    return {"success": True, "type": "flight_options", "options": options, "recommended": best, "order": pending["order"]}

def _mock_monitor_snapshot(seed: str, previous_wait: int = None) -> dict:
    if previous_wait is None:
        wait = _mock_int(seed + "wait", 6, 46)
    else:
        wait = max(0, previous_wait + _mock_int(seed + str(time.time()), -8, 5))
    has_slot = wait <= 12
    crowd = "低" if wait <= 10 else "中" if wait <= 25 else "高"
    return {
        "queue_wait_minutes": wait,
        "has_slot": has_slot,
        "crowd_level": crowd,
        "timestamp": int(time.time()),
        "message": "10分钟内可能有位" if has_slot else f"预计还需排队约{wait}分钟",
    }

def _mock_monitor_worker(monitor_id: str) -> None:
    for _ in range(4):
        time.sleep(1)
        with MOCK_MONITOR_LOCK:
            monitor = MOCK_RESOURCE_MONITORS.get(monitor_id)
            if not monitor:
                return
            prev = (monitor.get("latest") or {}).get("queue_wait_minutes")
            event = _mock_monitor_snapshot(monitor_id, prev)
            condition = monitor.get("condition", "")
            callback = monitor.get("callback_action", "")
            if event["has_slot"] and re.search(r"叫车|打车|提醒|有位", condition + callback):
                event["recommended_action"] = "现在叫车并前往，预计能赶上入座/拍照窗口"
            elif event["crowd_level"] == "高":
                event["recommended_action"] = "建议先去附近咖啡/低人流点位，稍后再回来"
            else:
                event["recommended_action"] = "继续监控，保持当前行程"
            monitor["latest"] = event
            monitor.setdefault("events", []).append(event)
    with MOCK_MONITOR_LOCK:
        monitor = MOCK_RESOURCE_MONITORS.get(monitor_id)
        if monitor:
            monitor["status"] = "completed"

def tool_mock_start_service_monitor(resource_type: str = "queue", target_name: str = "",
                                    city: str = "", condition: str = "",
                                    callback_action: str = "",
                                    duration_minutes: int = 30,
                                    user_context: dict = None) -> dict:
    """启动后台资源监控，模拟排队/有位/拥挤度动态变化。"""
    monitor_id = "MON-" + uuid.uuid4().hex[:8].upper()
    latest = _mock_monitor_snapshot(f"{city}|{target_name}|{condition}")
    if latest["queue_wait_minutes"] <= 12:
        latest["recommended_action"] = "低排队窗口，可以立刻前往"
    else:
        latest["recommended_action"] = "先执行周边备选，后台继续监控"
    monitor = {
        "monitor_id": monitor_id,
        "status": "running",
        "resource_type": resource_type or "queue",
        "target_name": target_name or "目标资源",
        "city": city,
        "condition": condition,
        "callback_action": callback_action,
        "duration_minutes": max(5, int(duration_minutes or 30)),
        "user_context": user_context or {},
        "created_at": int(time.time()),
        "latest": latest,
        "events": [latest],
        "sandbox": "mock_async_resource_monitor",
    }
    with MOCK_MONITOR_LOCK:
        MOCK_RESOURCE_MONITORS[monitor_id] = monitor
    threading.Thread(target=_mock_monitor_worker, args=(monitor_id,), daemon=True).start()
    return {"success": True, "monitor": monitor}

def tool_mock_get_monitor_status(monitor_id: str) -> dict:
    with MOCK_MONITOR_LOCK:
        monitor = MOCK_RESOURCE_MONITORS.get(monitor_id)
    if not monitor:
        return {"success": False, "error": "监控任务不存在或已结束"}
    return {"success": True, "monitor": monitor}

# ──────────────────────────────────────────────────────────────────────────────
# 环境感知动态定价引擎
# ──────────────────────────────────────────────────────────────────────────────
from datetime import datetime as _dt

PRICE_EVENT_PROFILES = {
    "rush_hour_morning": {
        "label": "工作日早高峰", "emoji": "🚇",
        "hours": [7, 8, 9],
        "surge_range": (1.3, 1.6),
        "demand": "high", "driver_availability": "low",
        "tip": "早高峰需求激增，建议提前15分钟叫车或选择地铁",
    },
    "rush_hour_evening": {
        "label": "工作日晚高峰", "emoji": "🚗",
        "hours": [17, 18, 19, 20],
        "surge_range": (1.4, 1.8),
        "demand": "high", "driver_availability": "low",
        "tip": "晚高峰为全天最贵时段，建议避开或提前叫车",
    },
    "concert_end": {
        "label": "演唱会/大型活动散场", "emoji": "🎵",
        "hours": [21, 22, 23],
        "surge_range": (1.8, 2.5),
        "demand": "extreme", "driver_availability": "very_low",
        "tip": "散场后约15-45分钟达到峰值，建议散场前30分钟叫车或散场1小时后再叫",
    },
    "rain": {
        "label": "雨天加价", "emoji": "🌧️",
        "hours": list(range(0, 24)),
        "surge_range": (1.3, 1.5),
        "demand": "high", "driver_availability": "medium",
        "tip": "雨天需求上升约40%，建议稍作等待或选择顺风车",
    },
    "holiday_peak": {
        "label": "节假日高峰", "emoji": "🎊",
        "hours": [9, 10, 14, 15, 16, 20, 21],
        "surge_range": (1.3, 1.6),
        "demand": "high", "driver_availability": "medium",
        "tip": "节假日出行高峰，建议错峰出行",
    },
    "new_year_eve": {
        "label": "跨年夜/除夕", "emoji": "🎆",
        "hours": [22, 23, 0, 1],
        "surge_range": (2.0, 3.0),
        "demand": "extreme", "driver_availability": "very_low",
        "tip": "全年最贵时段，建议提前3小时叫车或选择公共交通",
    },
    "late_night": {
        "label": "深夜时段", "emoji": "🌙",
        "hours": [0, 1, 2, 3, 4, 5],
        "surge_range": (1.2, 1.4),
        "demand": "medium", "driver_availability": "low",
        "tip": "深夜司机少，建议提前叫车，等待时间较长",
    },
    "airport_peak": {
        "label": "机场高峰", "emoji": "✈️",
        "hours": [6, 7, 8, 17, 18, 19, 20, 21],
        "surge_range": (1.2, 1.5),
        "demand": "high", "driver_availability": "medium",
        "tip": "机场接送高峰期，建议提前预约或选择接驳巴士",
    },
    "sports_event": {
        "label": "体育赛事散场", "emoji": "⚽",
        "hours": [21, 22, 23],
        "surge_range": (1.6, 2.2),
        "demand": "high", "driver_availability": "low",
        "tip": "赛事结束后大量人群同时离场，建议提前叫车或等候30分钟",
    },
    "typhoon": {
        "label": "台风/极端天气", "emoji": "🌀",
        "hours": list(range(0, 24)),
        "surge_range": (1.8, 2.5),
        "demand": "very_high", "driver_availability": "very_low",
        "tip": "极端天气下大量司机停运，建议改乘公共交通或延误出行",
    },
    "normal": {
        "label": "正常时段", "emoji": "✅",
        "hours": [10, 11, 12, 13, 14, 15, 16],
        "surge_range": (1.0, 1.1),
        "demand": "normal", "driver_availability": "high",
        "tip": "当前时段运力充足，现在叫车性价比最高",
    },
}

def get_environment_context(city: str, hour: int, event_type: str = "auto") -> dict:
    if event_type == "auto" or not event_type:
        if 7 <= hour <= 9:
            event_type = "rush_hour_morning"
        elif 17 <= hour <= 20:
            event_type = "rush_hour_evening"
        elif 0 <= hour <= 5:
            event_type = "late_night"
        else:
            event_type = "normal"
    profile = PRICE_EVENT_PROFILES.get(event_type, PRICE_EVENT_PROFILES["normal"])
    rng = random.Random(f"{city}{hour}{event_type}")
    surge = round(rng.uniform(*profile["surge_range"]) * 10) / 10
    return {
        "event_type": event_type,
        "event_label": profile["label"],
        "surge_factor": surge,
        "demand_level": profile["demand"],
        "driver_availability": profile["driver_availability"],
        "tip": profile["tip"],
        "emoji": profile["emoji"],
    }

def generate_price_timeline(base_price: int, city: str, primary_event: str = "normal") -> list:
    hour_info = {}
    for etype, profile in PRICE_EVENT_PROFILES.items():
        surge_mid = sum(profile["surge_range"]) / 2
        for h in profile["hours"]:
            if h not in hour_info or surge_mid > hour_info[h]["surge"]:
                hour_info[h] = {
                    "surge": surge_mid,
                    "event": profile["label"],
                    "emoji": profile["emoji"],
                    "event_type": etype,
                }
    if primary_event in PRICE_EVENT_PROFILES:
        profile = PRICE_EVENT_PROFILES[primary_event]
        surge_mid = sum(profile["surge_range"]) / 2
        for h in profile["hours"]:
            hour_info[h] = {
                "surge": surge_mid,
                "event": profile["label"],
                "emoji": profile["emoji"],
                "event_type": primary_event,
            }
    timeline = []
    for h in range(24):
        info = hour_info.get(h, {"surge": 1.0, "event": "正常时段", "emoji": "✅", "event_type": "normal"})
        timeline.append({
            "hour": h,
            "label": f"{h}时",
            "price": round(base_price * info["surge"]),
            "surge": round(info["surge"], 1),
            "event_label": info["event"],
            "emoji": info["emoji"],
            "event_type": info["event_type"],
            "is_optimal": False,
        })
    cheapest = sorted(timeline, key=lambda x: x["price"])[:3]
    opt_hours = {s["hour"] for s in cheapest}
    for slot in timeline:
        slot["is_optimal"] = slot["hour"] in opt_hours
    return timeline

def tool_simulate_price_scenario(
    service_type: str = "ride_hailing",
    city: str = "",
    origin: str = "",
    destination: str = "",
    event_type: str = "auto",
    target_hour: int = -1,
    user_context: dict = None,
) -> dict:
    """模拟不同时段/事件场景下的服务价格曲线，返回24小时价格轴与最优时段推荐。"""
    ctx = user_context or {}
    city = city or ctx.get("city", "")
    origin = origin or ctx.get("origin", "当前位置")
    destination = destination or ctx.get("destination", "目的地")
    now_hour = target_hour if 0 <= target_hour <= 23 else _dt.now().hour
    env = get_environment_context(city, now_hour, event_type)
    seed = f"{city}|{origin}|{destination}"
    distance_km = round(_mock_int(seed + "distance", 18, 86) / 10, 1)
    eta = _mock_int(seed + "eta", 3, 16)
    base_price = max(12, round(12 + distance_km * 2.8 + eta * 0.6))
    timeline = generate_price_timeline(base_price, city, env["event_type"])
    current_slot = timeline[now_hour]
    optimal = [s for s in timeline if s["is_optimal"]]
    best = optimal[0] if optimal else current_slot
    return {
        "success": True,
        "type": "price_simulation",
        "service_type": service_type,
        "city": city,
        "origin": origin,
        "destination": destination,
        "base_price": base_price,
        "distance_km": distance_km,
        "current_hour": now_hour,
        "current_env": env,
        "current_price": current_slot["price"],
        "current_surge": current_slot["surge"],
        "timeline": timeline,
        "optimal_windows": optimal,
        "best_window": best,
        "price_range": {
            "min": min(s["price"] for s in timeline),
            "max": max(s["price"] for s in timeline),
        },
        "potential_savings": max(s["price"] for s in timeline) - min(s["price"] for s in timeline),
        "recommendation": env["tip"],
        "primary_event": env["event_label"],
    }

# ──────────────────────────────────────────────────────────────────────────────
# 局部方案修改引擎（patch，不重新规划整个行程）
# ──────────────────────────────────────────────────────────────────────────────
_PATCH_POOLS = {
    "hotel": [
        {"suffix": " · 精品酒店",   "rating": "4.8", "cost_factor": 1.10, "tag": "精品酒店",   "reason": "评分4.8，比原选项高，距景区步行10分钟"},
        {"suffix": " · 高分民宿",   "rating": "4.9", "cost_factor": 1.05, "tag": "超高评分",   "reason": "评分4.9，本地热门民宿，可免费退改"},
        {"suffix": " · 品质连锁",   "rating": "4.7", "cost_factor": 0.92, "tag": "品质连锁",   "reason": "品牌连锁保障，性价比更高，免费停车"},
    ],
    "groupbuy": [
        {"suffix": " · 爆款套餐",   "rating": "4.8", "cost_factor": 0.85, "tag": "爆款团购",   "reason": "评分4.8，已售1000+，满意度95%"},
        {"suffix": " · 超值特惠",   "rating": "4.9", "cost_factor": 0.90, "tag": "限时特惠",   "reason": "本月最受欢迎，差评率低于2%，随时退款"},
        {"suffix": " · 口碑之选",   "rating": "4.7", "cost_factor": 0.95, "tag": "口碑榜TOP3", "reason": "本地口碑榜TOP3，退款无忧"},
    ],
    "restaurant": [
        {"suffix": " · 推荐餐厅",   "rating": "4.8", "cost_factor": 1.05, "tag": "推荐",       "reason": "美团评分4.8，环境优雅，上菜快"},
        {"suffix": " · 人气爆款",   "rating": "4.9", "cost_factor": 1.10, "tag": "人气爆款",   "reason": "本地人气TOP10，预约当天就能排到"},
        {"suffix": " · 实惠之选",   "rating": "4.6", "cost_factor": 0.80, "tag": "超值实惠",   "reason": "价格实惠，分量大，适合团体用餐"},
    ],
    "activity": [
        {"suffix": " · 热门景点",   "rating": "4.8", "cost_factor": 1.00, "tag": "热门",       "reason": "近期热度高，评分优秀，不建议跳过"},
        {"suffix": " · 高分打卡",   "rating": "4.9", "cost_factor": 1.05, "tag": "打卡爆款",   "reason": "出片率极高，小红书热推，建议下午去"},
    ],
}

def _make_replacement(item_type: str, old: dict, feedback: str, min_rating: float, max_price: int) -> dict:
    pool = _PATCH_POOLS.get(item_type, _PATCH_POOLS["hotel"])
    base = re.sub(r"[·\s]+.*$", "", old.get("name","")).strip() or "推荐选项"
    old_cost = _order_price(old.get("cost") or old.get("price"), 200)
    want_cheap = bool(re.search(r"贵|便宜|价格|省钱|预算", feedback))
    if want_cheap:
        chosen = min(pool, key=lambda p: p["cost_factor"])
    else:
        chosen = max(pool, key=lambda p: float(chosen["rating"]) if (chosen := p) else 0)
        chosen = max(pool, key=lambda p: float(p["rating"]))
    new_cost = max(50, round(old_cost * chosen["cost_factor"]))
    return {
        "name":     f"{base}{chosen['suffix']}",
        "rating":   chosen["rating"],
        "cost":     str(new_cost),
        "price":    str(new_cost),
        "address":  old.get("address",""),
        "photo_url":old.get("photo_url",""),
        "source":   "智能推荐",
        "is_real_meituan": False,
        "tag":      chosen["tag"],
        "reason":   chosen["reason"],
    }

def tool_patch_plan_item(
    item_type: str = "hotel",
    feedback: str = "",
    order_id: str = "",
    min_rating: float = 0.0,
    max_price: int = 0,
    city: str = "",
    user_context: dict = None,
) -> dict:
    """根据用户反馈实时替换行程中某个item（酒店/团购/餐厅），不重新规划整个行程。"""
    order = PENDING_ORDERS.get(order_id) if order_id else None
    old_item = {}
    hotel_options = []
    if order:
        it = order.get("item", {})
        if item_type == "hotel":
            old_item = it.get("hotel") or next((s for s in it.get("selected_items",[]) if s.get("type")=="hotel"), {})
            hotel_options = it.get("hotel_options", [])
        else:
            old_item = next((s for s in it.get("selected_items",[]) if s.get("type") in (item_type, "activity")), {})

    # Try existing hotel_options first (cycle)
    new_item = None
    if hotel_options and item_type == "hotel":
        candidates = [h for h in hotel_options if h.get("name") != old_item.get("name")]
        if candidates:
            want_cheap = bool(re.search(r"贵|便宜|价格|省钱", feedback))
            candidates.sort(key=lambda h: _order_price(h.get("cost"),9999) if want_cheap else -float(re.sub(r"[^\d.]","",str(h.get("rating","0")))or"0"))
            if min_rating:
                hq = [h for h in candidates if float(re.sub(r"[^\d.]","",str(h.get("rating","0")))or"0")>=min_rating]
                if hq: candidates = hq
            if max_price:
                hp = [h for h in candidates if _order_price(h.get("cost"),99999)<=max_price]
                if hp: candidates = hp
            new_item = candidates[0]
    if not new_item:
        new_item = _make_replacement(item_type, old_item, feedback, min_rating, max_price)

    # Patch stored order
    if order:
        it = order.get("item", {})
        if item_type == "hotel":
            it["hotel"] = new_item
            for i, s in enumerate(it.get("selected_items", [])):
                if s.get("type") == "hotel":
                    it["selected_items"][i] = {"type":"hotel","name":new_item.get("name",""),"price":new_item.get("cost",""),"rating":new_item.get("rating",""),"address":new_item.get("address",""),"photo_url":new_item.get("photo_url","")}
                    break
        else:
            for i, s in enumerate(it.get("selected_items", [])):
                if s.get("type") in (item_type, "activity"):
                    it["selected_items"][i] = {**s,"name":new_item.get("name",""),"price":new_item.get("cost",""),"rating":new_item.get("rating","")}
                    break

    TYPE_ZH = {"hotel":"酒店","groupbuy":"团购","restaurant":"餐厅","activity":"活动"}
    old_r = old_item.get("rating","-"); new_r = new_item.get("rating","-")
    old_p = old_item.get("cost") or old_item.get("price","-")
    new_p = new_item.get("cost") or new_item.get("price","-")
    tn = TYPE_ZH.get(item_type, item_type)
    return {
        "success": True,
        "type": "plan_patch",
        "item_type": item_type,
        "feedback": feedback,
        "order_id": order_id,
        "old_item": old_item,
        "new_item": new_item,
        "patch_summary": f'已将{tn}从"{old_item.get("name","-")}"(评分{old_r}，约¥{old_p})换为"{new_item.get("name","-")}"(评分{new_r}，约¥{new_p})',
        "reason": new_item.get("reason","已根据你的反馈更换为更优选项"),
    }

def _skill_python() -> str:
    return sys.executable or shutil.which("python") or shutil.which("python3") or "python3"

def _mttravel_exe() -> str:
    exe = shutil.which("mttravel")
    if exe:
        return exe
    for candidate in (
        os.path.expanduser("~/.npm-global/bin/mttravel"),
        "/usr/local/bin/mttravel",
        "/opt/homebrew/bin/mttravel",
    ):
        if os.path.exists(candidate):
            return candidate
    return ""

def _run_skill_command(cmd: list, cwd: str = "", timeout: int = REQUEST_TIMEOUT) -> dict:
    try:
        proc = subprocess.run(
            cmd,
            cwd=cwd or None,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        raw = (proc.stdout or "").strip()
        err = (proc.stderr or "").strip()
        data = None
        if raw:
            try:
                data = json.loads(raw)
            except Exception:
                data = None
        return {"ok": proc.returncode == 0, "data": data, "stdout": raw, "stderr": err, "code": proc.returncode}
    except Exception as e:
        return {"ok": False, "data": None, "stdout": "", "stderr": _safe_error_text(e), "code": -1}

def _meituan_skill_status() -> dict:
    venue_bind = os.path.join(MEITUAN_VENUE_SKILL_DIR, "scripts", "bind.py")
    coupon_auth = os.path.join(MEITUAN_COUPON_SKILL_DIR, "scripts", "auth.py")
    paotui_run = os.path.join(MEITUAN_PAOTUI_SKILL_DIR, "dist", "run.sh")
    status = {
        "travel": {
            "installed": os.path.isdir(MEITUAN_TRAVEL_SKILL_DIR),
            "cli_ready": bool(_mttravel_exe()),
            "token_ready": os.path.exists(os.path.expanduser("~/.config/meituan-travel/config.json")),
        },
        "venue": {
            "installed": os.path.exists(venue_bind),
            "bound": False,
        },
        "coupon": {
            "installed": os.path.exists(coupon_auth),
            "logged_in": False,
        },
        "paotui": {
            "installed": os.path.exists(paotui_run),
        },
    }
    if status["venue"]["installed"]:
        r = _run_skill_command([_skill_python(), venue_bind, "status"], MEITUAN_VENUE_SKILL_DIR, REQUEST_TIMEOUT)
        status["venue"]["bound"] = bool((r.get("data") or {}).get("valid"))
        status["venue"]["reason"] = (r.get("data") or {}).get("reason", "")
    if status["coupon"]["installed"]:
        r = _run_skill_command([_skill_python(), coupon_auth, "token-verify"], MEITUAN_COUPON_SKILL_DIR, REQUEST_TIMEOUT)
        status["coupon"]["logged_in"] = bool((r.get("data") or {}).get("valid"))
        status["coupon"]["reason"] = (r.get("data") or {}).get("reason", "")
    return status

def _real_meituan_items(result: dict, limit: int = 5) -> list:
    if not isinstance(result, dict) or not result.get("success"):
        return []
    items = result.get("results") or []
    normalized = []
    for x in items[:limit]:
        item = dict(x)
        if item.get("source") != "meituan_skill" or not item.get("is_real_meituan"):
            continue
        item.setdefault("rating", "4.6")
        item.setdefault("cost", item.get("price", ""))
        item["photo_url"] = item.get("photo_url", "")
        item.setdefault("booking_status", "美团真实数据")
        item.setdefault("advantage", item.get("type", "美团 Skill 返回"))
        item["data_level"] = "A_REAL_MEITUAN"
        item["can_order"] = True
        normalized.append(item)
    return normalized

def _meituan_cli_query(intent: str, city: str, keyword: str, filters: dict) -> str:
    filters = filters or {}
    parts = []
    if intent == "hotel_search":
        parts.append(f"{city}酒店推荐 真实酒店 店名 评分 价格")
    elif intent == "ticket_search":
        parts.append(f"{city}景点门票推荐 真实景点 店名 评分 价格")
    elif intent == "group_buy_query":
        parts.append("查询真实团购优惠")
    elif intent == "nearby_search":
        parts.append("查询附近真实商家")
    else:
        parts.append("查询真实餐厅")
    if keyword and keyword not in ("酒店", "景点 门票"):
        parts.append(keyword)
    if filters.get("location_hint"):
        parts.append(f"参考当前位置{filters['location_hint']}")
    if filters.get("sort_by") == "distance" or re.search(r"附近|最近|离我|周边", keyword or ""):
        parts.append("按距离从近到远")
    if filters.get("price_high"):
        parts.append(f"预算不超过{filters['price_high']}元")
    if filters.get("rating"):
        parts.append(f"评分不低于{filters['rating']}")
    return " ".join(parts)

def _extract_meituan_items_from_obj(obj, limit: int = 5) -> list:
    items = []
    name_keys = ("name", "title", "hotelName", "poiName", "shopName", "productName", "displayName")
    address_keys = ("address", "addr", "areaName", "poiAddress")
    rating_keys = ("rating", "score", "avgScore", "commentScore")
    cost_keys = ("cost", "price", "avgPrice", "priceText", "salePrice")

    def walk(node):
        if len(items) >= limit:
            return
        if isinstance(node, list):
            for x in node:
                walk(x)
            return
        if not isinstance(node, dict):
            return
        name = next((node.get(k) for k in name_keys if node.get(k)), "")
        if name:
            loc = (
                _extract_coord_pair(node)
                or _extract_coord_pair(node.get("location"))
                or _extract_coord_pair(node.get("coordinate"))
                or _extract_coord_pair(node.get("geo"))
            )
            item = {
                "name": str(name),
                "address": str(next((node.get(k) for k in address_keys if node.get(k)), "")),
                "rating": str(next((node.get(k) for k in rating_keys if node.get(k)), "")),
                "cost": str(next((node.get(k) for k in cost_keys if node.get(k)), "")),
                "distance": str(node.get("distance") or node.get("distanceText") or ""),
                "type": str(node.get("type") or node.get("category") or node.get("frontCategoryName") or ""),
                "booking_status": "美团真实数据",
                "advantage": str(node.get("recommendReason") or node.get("desc") or node.get("summary") or "美团 Skill 返回"),
                "source": "meituan_skill",
                "is_real_meituan": True,
            }
            if loc:
                item.update(loc)
            items.append(item)
        for value in node.values():
            walk(value)

    walk(obj)
    return items[:limit]

def _extract_meituan_items_from_text(text: str, limit: int = 5) -> list:
    items = []
    s = str(text or "")

    # ── 从 ## 章节标题追踪当前类型 ──
    lines = s.splitlines()
    line_section: dict[int, str] = {}
    cur_sec = "美团商家"
    for i, ln in enumerate(lines):
        h = re.match(r'##\s*[一二三四五六七八九十\d]+[、.。]\s*(.+)', ln)
        if h:
            cur_sec = re.sub(r'[*_`#]', '', h.group(1)).strip()
        line_section[i] = cur_sec

    def _sec_at(pos: int) -> str:
        line_no = s[:pos].count('\n')
        result = "美团商家"
        for li, sec in line_section.items():
            if li <= line_no:
                result = sec
        return result

    # ── 方法1：mttravel 标准格式  **名称**\n\n描述段落 ──
    # 名称行：整行只有 **text**（允许行首尾有空白）
    name_line_re = re.compile(r'(?:^|\n)[ \t]*\*\*([^*\n\d][^*\n]{1,60})\*\*[ \t]*\n')
    for m in name_line_re.finditer(s):
        if len(items) >= limit:
            break
        raw_name = m.group(1).strip()
        name = re.sub(r'[*_`\\]', '', raw_name).strip()
        if not name or len(name) < 2 or len(name) > 60:
            continue
        skip_words = r'小贴士|贴士|温馨提示|注意事项|总结|以下|更多|筛选|如果你'
        if re.search(skip_words, name):
            continue
        # 取名称行之后约 300 字作为描述
        desc_start = m.end()
        desc = s[desc_start: desc_start + 400].split('\n\n**')[0].strip()
        rating_m = re.search(r'(\d+\.\d+)\s*分', desc)
        rating = rating_m.group(1) if rating_m else ""
        price_m = re.search(r'([¥￥]\d[\d.,xX]*/?\S*)', desc)
        price = price_m.group(1) if price_m else ""
        addr_m = re.search(r'📍\s*([^\n]+)', desc) or re.search(r'地址[：:]\s*([^\n。]+)', desc)
        addr = addr_m.group(1).strip() if addr_m else ""
        items.append({
            "name": name,
            "address": addr,
            "rating": rating,
            "cost": price,
            "distance": "",
            "type": _sec_at(m.start()),
            "booking_status": "美团真实数据",
            "advantage": _clean_markdown(desc)[:200],
            "source": "meituan_skill",
            "is_real_meituan": True,
        })

    if items:
        return items

    # ── 方法2：## 标题型（酒店/旅游格式）──
    for block in re.split(r"\n(?=#+\s+)", s):
        if len(items) >= limit:
            break
        m_head = re.match(r"\s*#+\s+(.+?)\s*$", block.splitlines()[0] if block.splitlines() else "")
        if not m_head:
            continue
        name = re.sub(r"[*_`\\]", "", m_head.group(1)).strip()
        link_match = re.search(r"\[([^\]]+)\]\((https?://[^)]+)\)", block)
        link_text = re.sub(r"[*_`\\]", "", link_match.group(1)).strip() if link_match else ""
        if link_text and re.search(r"酒店|宾馆|民宿|旅舍|旅馆|客栈|Hotel", link_text):
            name = link_text
        if not name or len(name) > 60:
            continue
        if not re.search(r"评分|[¥￥][0-9]|价格|起/晚|返现|人均", block):
            continue
        m_rating = re.search(r"评分\s*([0-9.]+)", block)
        m_cost = re.search(r"([¥￥][0-9xX.]+[^ \t，,。]*)", block)
        m_addr = re.search(r"📍\s*([^\n]+)", block)
        items.append({
            "name": name,
            "address": m_addr.group(1).strip() if m_addr else "",
            "rating": m_rating.group(1) if m_rating else "",
            "cost": m_cost.group(1) if m_cost else "",
            "distance": "",
            "type": "美团酒店",
            "booking_status": "美团真实数据",
            "advantage": _clean_markdown(block)[:180],
            "source": "meituan_skill",
            "is_real_meituan": True,
        })
    for raw in str(text or "").splitlines():
        line = re.sub(r"!\[[^\]]*\]\([^)]+\)", "", raw).strip()
        line = re.sub(r"^\s*[-*•\d.、)）]+\s*", "", line)
        if not line:
            continue
        link_match = re.search(r"\[([^\]]+)\]\((https?://[^)]+)\)", line)
        link_text = ""
        link_url = ""
        if link_match:
            link_text = re.sub(r"[*_`\\]", "", link_match.group(1)).strip()
            link_url = link_match.group(2)
        if not link_text and len(line) > 160:
            continue
        if not re.search(r"酒店|宾馆|民宿|餐厅|饭店|面馆|小吃|门票|景区|乐园|馆|店", link_text or line):
            continue
        rating = ""
        m_rating = re.search(r"(?:美团真实评分|真实评分|评分)\s*([0-9.]+)", line)
        if m_rating:
            rating = m_rating.group(1)
        cost = ""
        m_cost = re.search(r"([¥￥][^ \t，,。]+)", line)
        if m_cost:
            cost = m_cost.group(1)
        if not link_text and not (m_rating or m_cost):
            continue
        name = link_text or re.split(r"[：:，,|｜]", line, 1)[0].strip()
        if not name or len(name) > 50 or re.search(r"小团|帮你|为你|作为|推荐|看看|下面|以下|评分|价格|距市中心|起/晚|返现", name):
            continue
        category = ""
        m_type = re.search(r"美团([\u4e00-\u9fa5A-Za-z0-9]+型|[\u4e00-\u9fa5A-Za-z0-9]+酒店|[\u4e00-\u9fa5A-Za-z0-9]+餐厅)", line)
        if m_type:
            category = m_type.group(1)
        items.append({
            "name": name,
            "address": "",
            "rating": rating,
            "cost": cost,
            "distance": "",
            "type": category,
            "booking_status": "美团真实数据",
            "advantage": line,
            "url": link_url,
            "source": "meituan_skill",
            "is_real_meituan": True,
        })
        if len(items) >= limit:
            break
    return items

def _call_meituan_travel_cli(intent: str, city: str, keyword: str,
                             filters: dict, limit: int) -> dict:
    exe = _mttravel_exe()
    if not exe:
        return {"success": False, "error": MEITUAN_SKILL_UNAVAILABLE, "detail": "mttravel not found"}
    config_path = os.path.expanduser("~/.config/meituan-travel/config.json")
    if not os.path.exists(config_path):
        return {"success": False, "error": MEITUAN_SKILL_UNAVAILABLE, "detail": "missing token config"}
    query = _meituan_cli_query(intent, city, keyword, filters or {})
    try:
        proc = subprocess.run(
            [exe, city or "", query],
            capture_output=True,
            text=True,
            timeout=int(os.environ.get("MEITUAN_CLI_TIMEOUT", str(MEITUAN_SKILL_TIMEOUT))),
        )
    except Exception as e:
        return {"success": False, "error": MEITUAN_SKILL_UNAVAILABLE, "detail": _safe_error_text(e)}
    raw = (proc.stdout or "").strip()
    err = (proc.stderr or "").strip()
    if proc.returncode != 0:
        return {"success": False, "error": MEITUAN_SKILL_UNAVAILABLE, "detail": err or raw}
    items = []
    try:
        items = _extract_meituan_items_from_obj(json.loads(raw), limit)
    except Exception:
        items = _extract_meituan_items_from_text(raw, limit)
    deduped = []
    seen_names = set()
    for item in items:
        name = (item.get("name") or "").strip()
        if not name or name in seen_names:
            continue
        seen_names.add(name)
        deduped.append(item)
    items = deduped[:limit]
    if not items:
        # mttravel 返回了自然语言文本但没有解析到结构化条目
        # 仍视为成功，把原始文本给 AI 直接使用
        if raw and len(raw) > 50:
            return {
                "success": True,
                "intent": intent,
                "city": city,
                "keyword": keyword,
                "count": 0,
                "results": [],
                "source": "meituan_skill",
                "is_real_meituan": True,
                "raw_text": raw,
                "note": "mttravel返回自然语言，请直接使用raw_text向用户展示",
            }
        return {"success": False, "error": MEITUAN_SKILL_UNAVAILABLE, "detail": "empty or unparsed mttravel result", "raw_text": raw}
    return {
        "success": True,
        "intent": intent,
        "city": city,
        "keyword": keyword,
        "count": len(items),
        "results": items,
        "source": "meituan_skill",
        "is_real_meituan": True,
        "raw_text": raw,
    }

def _call_meituan_venue_skill(intent: str, city: str, keyword: str, limit: int) -> dict:
    bind_script = os.path.join(MEITUAN_VENUE_SKILL_DIR, "scripts", "bind.py")
    if not os.path.exists(bind_script):
        return {"success": False, "error": MEITUAN_SKILL_UNAVAILABLE, "detail": "venue skill not found"}
    status = _run_skill_command([_skill_python(), bind_script, "status"], MEITUAN_VENUE_SKILL_DIR, REQUEST_TIMEOUT)
    if not (status.get("data") or {}).get("valid"):
        return {
            "success": False,
            "intent": intent,
            "city": city,
            "keyword": keyword,
            "source": "meituan_skill",
            "is_real_meituan": False,
            "error": "美团会场 Skill 尚未完成口令绑定，暂不能返回真实会场链接",
            "detail": (status.get("data") or {}).get("reason") or status.get("stderr", ""),
        }
    links = _run_skill_command([_skill_python(), bind_script, "get-links"], MEITUAN_VENUE_SKILL_DIR, REQUEST_TIMEOUT)
    data = links.get("data") or {}
    if not links.get("ok") or not data.get("success"):
        return {"success": False, "error": MEITUAN_SKILL_UNAVAILABLE, "detail": data.get("message") or links.get("stderr", "")}
    results = []
    for item in (data.get("links") or [])[:limit]:
        name = item.get("tenantName") or item.get("name") or "美团会场"
        results.append({
            "name": name,
            "address": city,
            "rating": "",
            "cost": "",
            "distance": "",
            "type": "美团会场链接",
            "booking_status": "美团真实链接",
            "advantage": keyword or "美团会场导购",
            "url": item.get("link", ""),
            "source": "meituan_skill",
            "is_real_meituan": True,
        })
    return {
        "success": True,
        "intent": intent,
        "city": city,
        "keyword": keyword,
        "count": len(results),
        "results": results,
        "source": "meituan_skill",
        "is_real_meituan": True,
    }

def _call_meituan_coupon_skill(intent: str, city: str, keyword: str, limit: int) -> dict:
    auth_script = os.path.join(MEITUAN_COUPON_SKILL_DIR, "scripts", "auth.py")
    issue_script = os.path.join(MEITUAN_COUPON_SKILL_DIR, "scripts", "issue.py")
    if not (os.path.exists(auth_script) and os.path.exists(issue_script)):
        return {"success": False, "error": MEITUAN_SKILL_UNAVAILABLE, "detail": "coupon skill not found"}
    auth = _run_skill_command([_skill_python(), auth_script, "token-verify"], MEITUAN_COUPON_SKILL_DIR, REQUEST_TIMEOUT)
    auth_data = auth.get("data") or {}
    if not auth_data.get("valid") or not auth_data.get("user_token"):
        return {
            "success": False,
            "intent": intent,
            "city": city,
            "keyword": keyword,
            "source": "meituan_skill",
            "is_real_meituan": False,
            "error": "美团领券 Skill 尚未登录，暂不能领取真实优惠券",
            "detail": auth_data.get("reason") or auth.get("stderr", ""),
        }
    issue = _run_skill_command([_skill_python(), issue_script, "--token", auth_data["user_token"]], MEITUAN_COUPON_SKILL_DIR, REQUEST_TIMEOUT)
    data = issue.get("data") or {}
    if not issue.get("ok") or data.get("success") is False:
        return {"success": False, "error": MEITUAN_SKILL_UNAVAILABLE, "detail": data.get("message") or issue.get("stderr", "")}
    coupons = data.get("coupons") or data.get("coupon_list") or []
    results = []
    for item in coupons[:limit]:
        results.append({
            "name": item.get("name") or item.get("couponName") or "美团优惠券",
            "address": city,
            "rating": "",
            "cost": item.get("discount_info") or item.get("discountInfo") or "",
            "distance": "",
            "type": "美团优惠券",
            "booking_status": item.get("valid_period") or item.get("validPeriod") or "已领取",
            "advantage": data.get("activity_name") or "美团真实领券结果",
            "url": data.get("activity_link") or "",
            "source": "meituan_skill",
            "is_real_meituan": True,
        })
    if not results and (data.get("activity_name") or data.get("activity_link")):
        results.append({
            "name": data.get("activity_name") or "美团优惠活动",
            "address": city,
            "rating": "",
            "cost": "",
            "distance": "",
            "type": "美团优惠活动",
            "booking_status": "美团真实活动",
            "advantage": "美团领券 Skill 返回",
            "url": data.get("activity_link", ""),
            "source": "meituan_skill",
            "is_real_meituan": True,
        })
    return {
        "success": True,
        "intent": intent,
        "city": city,
        "keyword": keyword,
        "count": len(results),
        "results": results,
        "source": "meituan_skill",
        "is_real_meituan": True,
    }

def _call_meituan_paotui_skill(intent: str, city: str, keyword: str,
                               user_lat: float = None, user_lng: float = None,
                               limit: int = 5) -> dict:
    run_script = os.path.join(MEITUAN_PAOTUI_SKILL_DIR, "dist", "run.sh")
    if not os.path.exists(run_script):
        return {"success": False, "error": MEITUAN_SKILL_UNAVAILABLE, "detail": "paotui skill not found"}
    cmd = ["sh", run_script, "search_poi", "--keyword", keyword or "美团跑腿", "--city", city or "北京"]
    if user_lat and user_lng:
        cmd.extend(["--lat", str(round(float(user_lat) * 1000000)), "--lng", str(round(float(user_lng) * 1000000))])
    poi = _run_skill_command(cmd, MEITUAN_PAOTUI_SKILL_DIR, REQUEST_TIMEOUT)
    if not poi.get("ok"):
        return {
            "success": False,
            "intent": intent,
            "city": city,
            "keyword": keyword,
            "source": "meituan_skill",
            "is_real_meituan": False,
            "error": "美团跑腿 Skill 暂不可用或尚未授权，暂不能生成真实跑腿草稿",
            "detail": poi.get("stderr") or poi.get("stdout", ""),
        }
    items = _extract_meituan_items_from_obj(poi.get("data") or {}, limit)
    if not items:
        return {"success": False, "error": MEITUAN_SKILL_UNAVAILABLE, "detail": "empty paotui result"}
    for item in items:
        item["type"] = item.get("type") or "美团跑腿地址"
        item["booking_status"] = "跑腿草稿待确认"
    return {
        "success": True,
        "intent": intent,
        "city": city,
        "keyword": keyword,
        "count": len(items),
        "results": items,
        "source": "meituan_skill",
        "is_real_meituan": True,
    }

def _pick_meituan_skill(intent: str, keyword: str) -> str:
    text = f"{intent} {keyword}"
    if re.search(r"跑腿|帮送|帮买|取快递|同城配送|送东西|寄文件|送合同", text):
        return "paotui"
    if re.search(r"领券|领红包|优惠券|美团券|红包|羊毛|福利|大额券|神券|隐藏券", text):
        return "coupon"
    if intent in ("hotel_search", "ticket_search") or re.search(r"酒店|宾馆|民宿|住宿|景点|门票|酒旅|旅行|旅游", text):
        return "travel"
    if intent in ("restaurant_search", "group_buy_query", "nearby_search", "booking_query") or re.search(r"外卖|点餐|送餐|闪购|买药|送药|会场|入口|团购|代金券|餐厅|饭店|美食|小吃|奶茶|咖啡|火锅|日料|川菜", text):
        return "venue"
    return "travel"

def _budget_breakdown(total_budget: int, days: int, distance_km: float) -> dict:
    days = max(1, int(days or 1))
    nights = max(1, days - 1)
    transport = min(round(total_budget * 0.13), 320)
    if distance_km > 500:
        transport = max(transport, min(round(total_budget * 0.28), 900))
    elif distance_km >= 50:
        transport = max(transport, 180)
    hotel = round(total_budget * (0.36 if days > 1 else 0.24))
    food = round(total_budget * 0.22)
    tickets = round(total_budget * 0.20)
    local = round(total_budget * 0.06)
    used = hotel + transport + food + tickets + local
    buffer = total_budget - used
    if buffer < 0:
        tickets = max(0, tickets + buffer)
        buffer = 0
    return {
        "total": total_budget,
        "hotel": hotel,
        "hotel_nightly_cap": max(180, round(hotel / nights)),
        "transport": transport,
        "food": food,
        "tickets": tickets,
        "local": local,
        "buffer": buffer,
        "nights": nights,
    }

def _adjust_budget_by_persona(budget: dict, pstate: dict) -> dict:
    out = dict(budget)
    weights = pstate.get("weights", {}) if isinstance(pstate, dict) else {}
    keys = pstate.get("keys", []) if isinstance(pstate, dict) else []
    total = int(out.get("total", 0) or 0)
    if total <= 0:
        return out
    if weights.get("budget_sensitive", 0) >= 0.85:
        out["hotel"] = round(out.get("hotel", 0) * 0.82)
        out["tickets"] = round(out.get("tickets", 0) * 0.78)
        out["local"] = round(out.get("local", 0) * 1.08)
    if weights.get("food_priority", 0) >= 0.9:
        out["food"] = round(out.get("food", 0) * 1.22)
        out["tickets"] = round(out.get("tickets", 0) * 0.9)
    if weights.get("photo_value", 0) >= 0.9:
        out["tickets"] = round(out.get("tickets", 0) * 1.12)
        out["local"] = round(out.get("local", 0) * 1.08)
    if "family" in keys or "elder" in keys:
        out["local"] = round(out.get("local", 0) * 1.25)
        out["buffer"] = round(out.get("buffer", 0) * 1.2)
    used = sum(out.get(k, 0) for k in ("hotel", "transport", "food", "tickets", "local"))
    out["buffer"] = max(0, total - used)
    out["hotel_nightly_cap"] = round(out.get("hotel", 0) / max(1, out.get("nights", 1)))
    return out

def _persona_itinerary_adjustment(city: str, day_index: int, tpl: dict, food: dict, state: dict) -> dict:
    c = city.replace("市", "")
    keys = state.get("keys", [])
    weights = state.get("weights", {})
    route = list(tpl.get("route", []))
    theme = tpl.get("theme", "")
    transport = tpl.get("transport", "")
    tip = tpl.get("tip", "")
    stay = "每个核心点停留 60-90 分钟"
    queue = "热门点排队超过 20 分钟就切换同片区备选"
    food_name = food.get("name") if _is_real_meituan_item(food) else ""

    if "special_force" in keys:
        theme = f"高效率压缩 · {theme}"
        route = route + [f"{c}夜景/夜骑点"] if day_index == 0 else route + [f"{c}高密度补点"]
        stay = "核心点快进快出，单点 35-50 分钟"
        queue = "排队超过 10 分钟直接跳过，优先把动线串满"
        transport = "地铁/高铁/打车组合，优先最快连接"
    elif "photo_hunter" in keys:
        theme = f"出片光线 · {theme}"
        route = route[:-1] + [f"{c}16:40日落机位", f"{c}18:20城市夜景", "审美咖啡店"] if len(route) >= 2 else route + [f"{c}日落机位", f"{c}夜景"]
        stay = "把日落前后 90 分钟留给拍摄"
        queue = "优先选有视野/光线的位置，排队长就换附近机位"
    elif "foodie" in keys:
        theme = f"美食动线 · {theme}"
        route = [route[0] if route else f"{c}酒店", "本地早餐", route[1] if len(route) > 1 else f"{c}核心景点", food.get("name") or f"{c}本地菜", "夜市/小吃街"]
        stay = "餐饮停留优先，景点压缩为顺路打卡"
        queue = "热门餐厅排队超过 30 分钟切换同菜系备选"
    elif "family" in keys:
        theme = f"家庭友好 · {theme}"
        route = route[:2] + [food_name or "亲子友好餐厅", "休息补给点"] if len(route) >= 2 else route + [food_name or "休息补给点"]
        stay = "每 90 分钟安排一次休息"
        queue = "避开长队项目，优先安全、洗手间和休息区"
        transport = "地铁/打车结合，减少长距离步行"
    elif "elder" in keys:
        theme = f"长辈轻松 · {theme}"
        route = route[:2] + ["茶馆/休息点"] if len(route) >= 2 else route + ["茶馆/休息点"]
        stay = "单日只保留 2-3 个核心点"
        queue = "尽量预约/错峰，减少换乘和上下楼"
        transport = "打车 + 短步行优先"
    elif "social_fear" in keys:
        theme = f"低人流 · {theme}"
        route = route[:2] + [food_name or "安静咖啡/小店"] if len(route) >= 2 else route + [food_name or "安静咖啡/小店"]
        stay = "错峰进入热门区域，少排队少社交"
        queue = "选择支路、小店和角落座位，避开人群高峰"
    elif "student" in keys:
        theme = f"省钱高性价比 · {theme}"
        route = ["免费/低价景点"] + route[1:] if route else [f"{c}免费景点", food_name or f"{c}平价小吃"]
        stay = "用步行/地铁换预算，保留拍照和小吃"
        queue = "优先免费景点和平价本地餐饮"
        transport = "地铁 + 步行优先"
    elif "relax" in keys or weights.get("comfort", 0) >= 0.8:
        theme = f"松弛慢游 · {theme}"
        route = route[:2] + [food_name or "湖边/街区咖啡", "傍晚慢逛"] if len(route) >= 2 else route + [food_name or "咖啡休息", "傍晚慢逛"]
        stay = "少景点、多停留，留足弹性时间"
        queue = "排队超过 20 分钟就换同街区备选"

    return {"theme": theme, "route": route, "transport": transport, "tip": f"{tip} {stay}；{queue}。".strip()}

def _build_day_schedule(route: list, food_name: str, transport: str,
                        persona_keys: list, day_index: int) -> list:
    """根据路线和人格生成带时间点的日程表。"""
    # 每种人格的起始时间和单点停留时长（分钟）
    if "special_force" in persona_keys:
        start_hour, start_min = 8, 0
        per_stop = 40
        lunch_dur = 30
    elif "photo_hunter" in persona_keys:
        start_hour, start_min = 6, 30   # 抢日出光线
        per_stop = 75
        lunch_dur = 45
    elif "elder" in persona_keys:
        start_hour, start_min = 9, 30
        per_stop = 100
        lunch_dur = 60
    elif "family" in persona_keys:
        start_hour, start_min = 9, 0
        per_stop = 80
        lunch_dur = 60
    elif "relax" in persona_keys:
        start_hour, start_min = 9, 30
        per_stop = 100
        lunch_dur = 60
    elif "social_fear" in persona_keys:
        start_hour, start_min = 8, 0   # 错峰早出
        per_stop = 90
        lunch_dur = 45
    elif "student" in persona_keys:
        start_hour, start_min = 8, 30
        per_stop = 60
        lunch_dur = 40
    elif "foodie" in persona_keys:
        start_hour, start_min = 9, 0
        per_stop = 60
        lunch_dur = 80
    else:
        start_hour, start_min = 9, 0
        per_stop = 75
        lunch_dur = 50

    transit_min = 25  # 平均交通时间

    schedule = []
    cur_h, cur_m = start_hour, start_min

    def fmt(h, m):
        return f"{h:02d}:{m:02d}"

    def advance(minutes):
        nonlocal cur_h, cur_m
        cur_m += minutes
        while cur_m >= 60:
            cur_m -= 60
            cur_h += 1

    # 出发准备（仅第一天）
    if day_index == 0:
        schedule.append({"time": fmt(cur_h, cur_m), "activity": "整理行李出发", "type": "transit", "duration_min": 20})
        advance(20)

    stops = [s for s in (route or []) if s and "返程" not in s]

    for idx, stop in enumerate(stops):
        # 前往交通
        if idx > 0 or day_index > 0:
            schedule.append({"time": fmt(cur_h, cur_m), "activity": f"前往{stop}", "type": "transit", "duration_min": transit_min})
            advance(transit_min)

        # 午餐插入：在第2-3个景点之间（11:30-13:30区间）
        if idx == max(1, len(stops) // 2) and food_name:
            # 如果当前时间在午餐时间窗口附近
            cur_total = cur_h * 60 + cur_m
            if 690 <= cur_total <= 840:  # 11:30 ~ 14:00
                schedule.append({"time": fmt(cur_h, cur_m), "activity": f"午餐：{food_name}", "type": "food", "duration_min": lunch_dur})
                advance(lunch_dur)

        # 活动本体
        stop_dur = per_stop
        if "photo_hunter" in persona_keys and idx == len(stops) - 1:
            # 最后一站留给日落
            schedule.append({"time": fmt(cur_h, cur_m), "activity": f"{stop}（等待日落光线）", "type": "sight", "duration_min": 90})
            advance(90)
        else:
            schedule.append({"time": fmt(cur_h, cur_m), "activity": stop, "type": "sight", "duration_min": stop_dur})
            advance(stop_dur)

        # family/elder 在午后加一次休息
        if idx == len(stops) // 2 and ("family" in persona_keys or "elder" in persona_keys):
            if cur_h >= 13:
                schedule.append({"time": fmt(cur_h, cur_m), "activity": "茶歇/休息", "type": "rest", "duration_min": 30})
                advance(30)

    # 如果午餐没有在循环里插入（路线太短），补在最后
    if food_name and not any(s["type"] == "food" for s in schedule):
        schedule.append({"time": fmt(cur_h, cur_m), "activity": f"晚餐：{food_name}", "type": "food", "duration_min": lunch_dur})
        advance(lunch_dur)

    # 特种兵追加夜景
    if "special_force" in persona_keys and day_index == 0:
        schedule.append({"time": fmt(cur_h, cur_m), "activity": "夜景/夜骑打卡", "type": "sight", "duration_min": 60})

    # 松弛/出片：傍晚漫步
    if ("relax" in persona_keys or "photo_hunter" in persona_keys) and cur_h < 18:
        schedule.append({"time": "18:00", "activity": "傍晚街区漫步", "type": "relax", "duration_min": 60})

    return schedule


_RAIN_WMO_CODES = {51,53,55,61,63,65,71,73,75,77,80,81,82,85,86,95,96,99}

def _weather_is_rainy(weather: dict) -> bool:
    """判断天气是否为雨雪天，用于触发室内调整。"""
    if not weather or not weather.get("success"):
        return False
    text = weather.get("data", {}).get("text", "")
    return any(kw in text for kw in ("雨", "雪", "雷", "冰雹"))

def _apply_rain_indoor_swap(route: list, city: str) -> tuple[list, str]:
    """将路线中的纯户外景点替换为室内备选，返回新路线和提示。"""
    outdoor_kw = ["公园", "山", "湖", "海滩", "广场", "露天", "户外"]
    indoor_alternatives = {
        "上海": ["上海博物馆", "豫园商城(室内)", "外滩观光隧道"],
        "北京": ["故宫博物院(室内展馆)", "国家博物馆", "798艺术区室内展览"],
        "杭州": ["浙江省博物馆", "良渚博物院", "西湖文化广场(室内)"],
        "苏州": ["苏州博物馆(室内)", "苏绣艺术博物馆", "苏州丝绸博物馆"],
        "新加坡": ["滨海湾花园室内云雾森林", "新加坡国家博物馆", "滨海艺术中心"],
    }
    c = city.replace("市", "")
    alts = indoor_alternatives.get(c, [f"{c}室内博物馆", f"{c}商场/购物中心"])
    new_route = []
    swapped = 0
    for stop in route:
        if any(kw in stop for kw in outdoor_kw) and swapped < len(alts):
            new_route.append(alts[swapped])
            swapped += 1
        else:
            new_route.append(stop)
    note = f"🌧️ 天气预警：当日有雨，已将{swapped}个户外景点替换为室内备选，行程依然完整可执行。" if swapped else ""
    return new_route, note

def _build_itinerary_days(city: str, days: int, sights: list, foods: list,
                          transport_mode: str, budget: dict,
                          persona_state: dict = None, weather: dict = None) -> list:
    c = city.replace("市", "")
    real_sights = [x for x in sights if _is_real_meituan_item(x)]
    real_foods = [x for x in foods if _is_real_meituan_item(x)]
    area_sights = [x for x in sights if x.get("is_area_suggestion")]
    area_foods = [x for x in foods if x.get("is_area_suggestion")]

    def pick(items, idx, fallback):
        if not items:
            return fallback
        return items[idx % len(items)].get("name") or fallback

    if real_sights or real_foods:
        base = [
            {
                "theme": "真实资源开场",
                "route": [
                    f"{c}交通枢纽/酒店",
                    pick(real_sights or area_sights, 0, f"{c}代表性景区区域"),
                    pick(real_foods or area_foods, 0, f"{c}餐饮区域建议"),
                    pick(real_sights or area_sights, 1, f"{c}夜游区域"),
                ],
                "transport": transport_mode,
                "tip": "优先使用工具返回的真实商户/景点，区域建议只作补位。",
            },
            {
                "theme": "真实餐饮与街区",
                "route": [
                    pick(real_sights or area_sights, 1, f"{c}文化街区区域"),
                    pick(real_foods or area_foods, 1, f"{c}小吃区域建议"),
                    pick(real_sights or area_sights, 2, f"{c}夜景区域"),
                ],
                "transport": "地铁/打车 + 步行",
                "tip": "餐饮和活动按评分、价格、距离与状态权重排序。",
            },
            {
                "theme": "轻松返程",
                "route": [
                    pick(real_sights or area_sights, 2, f"{c}低强度游览区域"),
                    pick(real_foods or area_foods, 2, f"{c}伴手礼/早餐区域"),
                    "返程",
                ],
                "transport": "公共交通 + 枢纽接驳",
                "tip": "返程日减少折返，保留机动时间。",
            },
        ]
    else:
        templates = {
            "苏州": [
                {"theme":"园林与老城开场","route":["苏州站/酒店","拙政园","苏州博物馆","平江路"],"transport":"高铁到达后地铁/打车 + 老城步行","tip":"苏博和拙政园放同一天，减少折返。"},
                {"theme":"古寺园林 + 夜游","route":["寒山寺","留园","七里山塘"],"transport":"地铁 + 短途打车 + 步行","tip":"山塘街安排傍晚后，夜景更稳。"},
                {"theme":"湖景轻松收尾","route":["金鸡湖","诚品书店","返程"],"transport":"地铁为主，返程预留60分钟","tip":"第三天不塞太满，避免赶车。"},
                {"theme":"同里/木渎备选扩展","route":["酒店","同里古镇或木渎古镇","市区晚餐"],"transport":"地铁/市郊车 + 打车补充","tip":"多一天时再启用，不挤占主线。"},
            ]
        }
        base = templates.get(c, [
            {"theme":"区域建议开场","route":[f"{c}交通枢纽/酒店", pick(area_sights, 0, f"{c}代表性景区区域"), pick(area_foods, 0, f"{c}餐饮区域建议")],"transport":transport_mode,"tip":"工具未返回真实商户时，只展示区域建议，不生成具体商户订单。"},
            {"theme":"文化街区与餐饮区域","route":[pick(area_sights, 1, f"{c}文化街区区域"), pick(area_foods, 1, f"{c}餐饮区域建议"), f"{c}夜游区域"],"transport":"地铁/打车 + 步行","tip":"区域建议不代表具体商户，现场可用地图二次筛选。"},
            {"theme":"轻松返程","route":[pick(area_sights, 2, f"{c}低强度游览区域"), "伴手礼区域", "返程"],"transport":"公共交通 + 枢纽接驳","tip":"返程日保留机动时间。"},
        ])
    out = []
    day_ticket = round((budget.get("tickets", 0) or 0) / max(1, days))
    day_food = round((budget.get("food", 0) or 0) / max(1, days))
    day_local = round((budget.get("local", 0) or 0) / max(1, days))
    pstate = persona_state or _persona_state("relax")
    rainy = _weather_is_rainy(weather)
    for i in range(days):
        tpl = base[i % len(base)]
        food = foods[i % len(foods)] if foods else {}
        tpl = _persona_itinerary_adjustment(c, i, tpl, food, pstate)
        rain_note = ""
        if rainy and i == 0:  # 只对第一天（当天）做室内替换
            new_route, rain_note = _apply_rain_indoor_swap(tpl["route"], c)
            tpl = dict(tpl)
            tpl["route"] = new_route
        food_name = food.get("name", f"{c}餐饮区域建议")
        schedule = _build_day_schedule(tpl["route"], food_name, tpl["transport"], pstate.get("keys", []), i)
        out.append({
            "day": i + 1,
            "theme": tpl["theme"],
            "route": tpl["route"],
            "schedule": schedule,
            "food": food_name,
            "food_cost": food.get("cost", ""),
            "food_source": food.get("source", "local_reference"),
            "food_is_real_meituan": _is_real_meituan_item(food),
            "food_note": "真实商户" if _is_real_meituan_item(food) else "区域建议，不代表具体商户",
            "transport": tpl["transport"],
            "budget": day_ticket + day_food + day_local + (round((budget.get("transport", 0) or 0) / 2) if i in (0, days - 1) else 0),
            "tip": tpl["tip"],
            "rain_note": rain_note,
        })
    return out

def _route_card_from_trip(origin: dict, dest: dict, req: dict, days: list,
                          budget: dict, persona_state: dict, decision: dict,
                          primary_transport: str, resource_quality: dict = None) -> dict:
    city = dest.get("name") or req.get("destination") or "目的地"
    labels = [str(x).replace("状态", "") for x in (persona_state.get("labels") or [])]
    persona_label = labels[0] if labels else "松弛感"
    day = days[0] if days else {}
    route = [x for x in (day.get("route") or []) if x]
    if not route:
        route = ["集合/出发点", city]
    route = route[:5]
    if route and ("交通枢纽" in route[0] or "酒店" in route[0]):
        route[0] = "集合/出发点"
    if route and route[0] == city:
        route[0] = "集合/出发点"
    if not route or route[0] != "集合/出发点":
        route = ["集合/出发点"] + route
    real_counts = (resource_quality or {}).get("real_counts") or {}
    has_real_resource = bool((resource_quality or {}).get("use_real_results") or sum(real_counts.values() or [0]))
    transport_plan = []
    regional = (decision or {}).get("scope") == "regional"
    for i in range(max(0, len(route) - 1)):
        if i == 0:
            first_mode = "高铁/接驳" if regional else ("骑行" if "骑" in str(primary_transport) else "地铁/打车")
            transport_plan.append((first_mode, 35 if regional else 20))
        elif i == 1:
            transport_plan.append(("步行", 10))
        else:
            transport_plan.append(("打车", 15 if i % 2 == 0 else 20))
    def _step_type(name: str, idx: int) -> str:
        if idx == 0:
            return "集合"
        if re.search(r"餐|吃|小吃|夜市|茶|咖啡|美食", name):
            return "餐饮"
        if re.search(r"沙滩|海|湖|环岛|慢行|夜景|夜游", name):
            return "景点"
        return "景点"
    route_map = []
    for idx, name in enumerate(route):
        nxt = transport_plan[idx] if idx < len(transport_plan) else ("", 0)
        route_map.append({
            "step": idx + 1,
            "name": name,
            "type": _step_type(name, idx),
            "stay_minutes": 0 if idx == 0 else (90 if idx == len(route) - 1 else 70),
            "short_desc": "按当前位置/集合点出发" if idx == 0 else "",
            "next_transport": nxt[0],
            "next_duration_minutes": nxt[1],
            "data_source": "meituan_skill" if has_real_resource else "baidu_map_or_area_reference",
            "is_real_poi": has_real_resource,
            "need_verify": not has_real_resource,
        })
    total_minutes = sum(x.get("stay_minutes", 0) for x in route_map) + sum(x[1] for x in transport_plan)
    if total_minutes < 300:
        total_minutes = 420 if req.get("days", 1) == 1 else total_minutes
    intensity = "高" if "special_force" in (persona_state.get("keys") or []) else ("低" if "elder" in (persona_state.get("keys") or []) else "中低")
    confidence = "真实资源优先" if has_real_resource else "区域建议"
    timeline = []
    hour, minute = 10, 0
    for item in route_map:
        timeline.append({"time": f"{hour:02d}:{minute:02d}", "title": item["name"], "detail": item["type"], "cost": ""})
        minute += item.get("stay_minutes", 0) + (item.get("next_duration_minutes") or 0)
        hour += minute // 60
        minute %= 60
    actions = [
        {"label": "更省钱", "action_type": "refine_budget"},
        {"label": "更松弛", "action_type": "refine_relax"},
        {"label": "特种兵", "action_type": "refine_special_force"},
        {"label": "避开排队", "action_type": "avoid_queue"},
        {"label": "加酒店", "action_type": "add_hotel", "requires_confirm": False},
    ]
    return {
        "answer_type": "map_first_trip_plan",
        "summary": f"🍊 {city} {req.get('days', 1)} 日{persona_label}路线",
        "route_map": route_map,
        "metrics": {
            "total_duration_minutes": total_minutes,
            "total_budget": budget.get("total"),
            "budget_range": f"约 ¥{max(200, round((budget.get('total') or 800) * 0.6))}-{budget.get('total') or 800}",
            "route_intensity": intensity,
            "walking_intensity": intensity,
            "queue_risk": "热门点排队，中午错峰",
            "data_confidence": confidence,
        },
        "timeline": timeline,
        "fallbacks": [
            {"trigger": "热门点排队", "backup_plan": "中午错峰；排队超过20分钟切换同片区备选。"},
            {"trigger": "天气/打车拥堵", "backup_plan": "优先室内点或地铁接驳，保留机动时间。"},
        ],
        "actions": actions,
    }

def tool_plan_meituan_trip(city: str, user_prompt: str,
                           persona: str = "", map_provider: str = "") -> dict:
    req = _extract_trip_requirements(user_prompt, city)
    soul_memory = req.get("soul_memory", {})
    soul_prefs = soul_memory.get("preferences", {}) or {}
    soul_food = soul_prefs.get("food", {}) if isinstance(soul_prefs, dict) else {}
    pstate = _persona_state(persona, user_prompt)
    origin = _resolve_place_info(req["origin"], city)
    dest = _resolve_place_info(req["destination"], city)
    distance_km = _geo_distance_km(origin, dest)
    decision = _judge_travel_scope(origin, dest, distance_km)
    flight_requested = _wants_flight_travel(user_prompt)
    bike_requested = _wants_bike_transport(user_prompt)
    if flight_requested:
        decision = dict(decision)
        decision["flight_query"] = True
        if decision.get("scope") in ("cross_country", "long_distance"):
            decision["priority"] = "飞机/航班查询优先"
    if bike_requested and decision.get("scope") in ("same_city_cross_area", "short"):
        decision = dict(decision)
        decision["priority"] = "按用户要求优先骑行，地铁/打车/步行保留备选"
    long_legs, local_legs, backup_legs = _build_panorama_legs(origin, dest, distance_km, decision, flight_requested, bike_requested)
    trip_map_urls = _panorama_map_urls(origin, dest)
    flight_query = _flight_query_info(origin, dest, trip_map_urls, distance_km, decision, flight_requested)
    primary_transport = (long_legs[0]["mode"] if long_legs else (local_legs[0]["mode"] if local_legs else "步行"))
    budget = _adjust_budget_by_persona(_budget_breakdown(req["budget"], req["days"], distance_km), pstate)
    proactive = _proactive_butler_defaults(req, decision, pstate, user_prompt, dest.get("name", ""))
    hotel_filter = {"price_high": budget["hotel_nightly_cap"], "rating": 4.5}
    food_keyword = "本地菜 小吃 不辣" if soul_food.get("avoid_spicy") else "本地菜 小吃"
    food_filter = {
        "price_high": max(40, round(budget["food"] / max(1, req["days"]))),
        "avoid_spicy": bool(soul_food.get("avoid_spicy")),
    }
    independent = req["planner_mode"] == "independent_trip"
    futures = {}
    results = {}
    if independent:
        can_use_meituan_resources = not req.get("user_preference", {}).get("avoid_meituan")
        with ThreadPoolExecutor(max_workers=3 if can_use_meituan_resources else 2) as pool:
            futures["weather"] = pool.submit(_weather_aux, dest.get("name") or req["destination"])
            if can_use_meituan_resources:
                futures["foods"] = pool.submit(tool_call_meituan_skill, "restaurant_search", dest.get("name",""), food_keyword, "", None, None, food_filter, 6)
                futures["sights"] = pool.submit(tool_call_meituan_skill, "ticket_search", dest.get("name",""), "景点 门票", "", None, None, {"price_high": max(80, round(budget["tickets"] / max(1, req["days"])))}, 6)
            try:
                results["weather"] = futures["weather"].result(timeout=REQUEST_TIMEOUT + 1)
            except Exception as e:
                results["weather"] = {"success": False, "error": _safe_error_text(e)}
            if can_use_meituan_resources:
                for key in ("foods", "sights"):
                    try:
                        results[key] = futures[key].result(timeout=MEITUAN_SKILL_TIMEOUT)
                    except Exception as e:
                        results[key] = {"success": False, "error": _safe_error_text(e)}
        hotels = []
        foods = _attach_item_coords(_real_meituan_items(results.get("foods", {}), 6), dest.get("name","")) if can_use_meituan_resources else []
        sights = _attach_item_coords(_real_meituan_items(results.get("sights", {}), 6), dest.get("name","")) if can_use_meituan_resources else []
        if not foods:
            foods = _attach_item_coords(_independent_items("restaurant_search", dest.get("name",""), food_keyword, food_filter, 6), dest.get("name",""))
        if not sights:
            sights = _attach_item_coords(_independent_items("ticket_search", dest.get("name",""), "景点 门票", {}, 6), dest.get("name",""))
    else:
        with ThreadPoolExecutor(max_workers=4) as pool:
            futures["weather"] = pool.submit(_weather_aux, dest.get("name") or req["destination"])
            futures["hotels"] = pool.submit(tool_call_meituan_skill, "hotel_search", dest.get("name",""), "酒店", "", None, None, hotel_filter, 3)
            futures["foods"] = pool.submit(tool_call_meituan_skill, "restaurant_search", dest.get("name",""), food_keyword, "", None, None, food_filter, 6)
            futures["sights"] = pool.submit(tool_call_meituan_skill, "ticket_search", dest.get("name",""), "景点 门票", "", None, None, {"price_high": max(80, round(budget["tickets"] / max(1, req["days"])))}, 6)
            for key, fut in futures.items():
                try:
                    wait_time = REQUEST_TIMEOUT + 1 if key == "weather" else MEITUAN_SKILL_TIMEOUT
                    results[key] = fut.result(timeout=wait_time)
                except Exception as e:
                    results[key] = {"success": False, "error": _safe_error_text(e)}
        hotels = _attach_item_coords(_real_meituan_items(results.get("hotels", {}), 3), dest.get("name",""))
        foods = _attach_item_coords(_real_meituan_items(results.get("foods", {}), 6), dest.get("name",""))
        sights = _attach_item_coords(_real_meituan_items(results.get("sights", {}), 6), dest.get("name",""))
        real_result_available = bool(hotels or foods or sights)
        fallback_used = False
        recovery_message = ""
        if not real_result_available:
            recovery_message = "🍊 已从米其林知识库、百度地图等多源精选推荐，含评分与位置信息。"
            for item in (results.get("hotels"), results.get("foods"), results.get("sights")):
                if isinstance(item, dict) and item.get("city_guard") == "blocked_cross_city_results":
                    recovery_message = item.get("message") or recovery_message
                    break
            fallback_used = True
        if not foods:
            foods = _attach_item_coords(_independent_items("restaurant_search", dest.get("name",""), "餐饮区域建议", {}, 6), dest.get("name",""))
        if not sights:
            sights = _attach_item_coords(_independent_items("ticket_search", dest.get("name",""), "景点区域建议", {}, 6), dest.get("name",""))
        resource_quality = _resource_data_tier(hotels, foods, sights)
        if resource_quality["tier"] != "A":
            fallback_used = True
    days = _build_itinerary_days(dest.get("name",""), req["days"], sights, foods, primary_transport, budget, pstate, results.get("weather"))
    title_suffix = "独立行程规划" if req["intent"] == "no_meituan" else "行程规划"
    if independent:
        resource_quality = _resource_data_tier(hotels, foods, sights)
        recovery_message = ""
        fallback_used = bool(resource_quality.get("area_suggestion_count"))
    route_card = _route_card_from_trip(origin, dest, req, days, budget, pstate, decision, primary_transport, resource_quality)
    trip_route_points = [
        {"lat": origin.get("lat"), "lng": origin.get("lng")},
        {"lat": dest.get("lat"), "lng": dest.get("lng")},
    ]
    map_data = _build_map_data(dest, trip_route_points, [
        {"category": "origin", "items": [origin]},
        {"category": "destination", "items": [dest]},
        {"category": "hotel", "items": hotels},
        {"category": "food", "items": foods},
        {"category": "sight", "items": sights},
    ])
    pending_order = {}
    if not independent and resource_quality.get("tier") == "A":
        pending = tool_create_pending_order(
            "trip_bundle",
            _build_trip_bundle_item(dest, req, budget, hotels, foods, sights),
            {
                "destination": dest.get("name",""),
                "days": req["days"],
                "budget": req["budget"],
                "persona": ",".join(pstate.get("keys", [])),
                "persona_label": " + ".join(pstate.get("labels", [])),
                "source": "meituan_skill",
            }
        )
        if pending.get("success"):
            pending_order = pending["order"]
    soul_summary = str(soul_memory.get("summary", "暂无稳定偏好"))
    if len(soul_summary) > 46:
        soul_summary = soul_summary[:46] + "…"
    planning_context = {
        "user_request": user_prompt,
        "persona": pstate,
        "city": dest.get("name", req.get("destination", "")),
        "budget": budget,
        "weather": results.get("weather"),
        "route": {"distance_km": distance_km, "decision": decision, "transport": primary_transport},
        "meituan_hotels": [x for x in hotels if _is_real_meituan_item(x)],
        "meituan_restaurants": [x for x in foods if _is_real_meituan_item(x)],
        "meituan_spots": [x for x in sights if _is_real_meituan_item(x)],
        "area_suggestions": [x for x in [*hotels, *foods, *sights] if x.get("is_area_suggestion")],
        "data_quality": resource_quality,
        "soul_memory": soul_memory,
        "order": pending_order,
        "route_card": route_card,
    }
    return {
        "success": True,
        "type": "independent_trip_plan" if independent else "meituan_trip_plan",
        "intent": req["intent"],
        "commerce_mode": req["commerce_mode"],
        "planner_mode": req["planner_mode"],
        "user_preference": req["user_preference"],
        "cta": req["cta"],
        "persona_state": pstate,
        "proactive_defaults": proactive,
        "persona": ",".join(pstate.get("keys", [])),
        "persona_label": " + ".join(pstate.get("labels", [])),
        "title": f"{dest.get('name')}{req['days']}天{title_suffix}" if independent else f"{dest.get('name')} {req['days']}天{req['budget']}元平台资源行程",
        "summary": f"已根据预算、路线和{'+'.join(pstate.get('labels', []))}自动完成独立行程规划。" if independent else f"核心需求已锁定：{dest.get('name')}、{req['days']}天、总预算{req['budget']}元，并按{'+'.join(pstate.get('labels', []))}联动平台资源。",
        "requirements": req,
        "soul_memory": soul_memory,
        "origin": origin,
        "destination": dest,
        "distance_km": distance_km,
        "decision": decision,
        "transport": {
            "primary": primary_transport,
            "long_distance": long_legs,
            "local_transfer": local_legs,
            "short_backup": backup_legs,
            "flight_query": flight_query,
        },
        "weather": results.get("weather") if isinstance(results.get("weather"), dict) else {"available": False, "text": "天气暂不可用，仅作辅助。"},
        "hotels": hotels,
        "foods": foods,
        "sights": sights,
        "days": days,
        "route_card": route_card,
        "budget": budget,
        "fallback_used": fallback_used,
        "fallback_message": (recovery_message or "🍊 已从多源精选推荐，区域建议已用位置标注。") if fallback_used else "",
        "data_quality": resource_quality,
        "planning_context": planning_context,
        "map_provider": _detect_map_provider(user_prompt, map_provider or "gaode"),
        "map_urls": trip_map_urls,
        "flight_query": flight_query,
        "map_data": map_data,
        "pending_order": pending_order,
        "hermes_skill": _hermes_skill_status(),
        "status_flow": [
            proactive.get("intro", "我先生成可执行草案，不打断你。"),
            f"已默认：{'、'.join(proactive.get('assumptions', []))}",
            *[f"✅ {step}" for step in proactive.get("workflow", [])],
            f"已提取核心需求：{dest.get('name')} · {req['days']}天 · 预算{req['budget']}元",
            f"Soul记忆已加载：{soul_summary}",
            f"已按状态权重生成动线：{' + '.join(pstate.get('labels', []))}",
            "Hermes 技能记忆已参与规划决策" if _hermes_skill_status().get("enabled") else "Hermes 技能未启用，使用本地规则规划",
            "Independent Planner 已接管" if independent else "已按需匹配美团资源",
            f"已按距离判定主交通：{decision.get('priority')}",
            "已接入航班查询入口" if flight_query.get("enabled") else "当前距离无需航班查询",
            "已生成待确认订单，等待用户确认" if pending_order else ("未生成订单：当前不是完整真实资源规划" if not independent else "无需订单动作，保留规划闭环"),
            "天气已作为辅助信息补充，未覆盖行程主线",
        ],
        "planner_route": {
            "selected": "independent_trip_planner" if independent else "meituan_commerce_planner",
            "called_tools": (["call_meituan_skill"] if independent and not req["user_preference"].get("avoid_meituan") else []) if independent else ["call_meituan_skill"],
            "blocked": (["plan_meituan_trip", "call_meituan_skill"] if req["user_preference"].get("avoid_meituan") else ["meituan_order_flow"]) if independent else [],
            "reason": ("avoid_meituan=true，使用独立行程规划" if req["user_preference"].get("avoid_meituan") else "用户未要求美团交易，默认使用独立行程规划") if independent else "用户需要平台资源推荐",
        },
        "meituan_note": "已根据预算和路线自动完成独立行程规划" if independent else (("美团搜索🔍 未返回完整真实资源，区域建议已明确标注" if fallback_used else "已按你的要求联动美团实时资源")),
        "fixed_sections": ["行程速览", "天气速览卡片", "景点与餐饮建议" if req["commerce_mode"] == "none" else "美团酒店推荐", "几天行程路线卡片", "综合结论"],
    }

WEEKEND_CITY_PLANS = {
    "杭州": {
        "title": "杭州西湖半日 Citywalk",
        "summary": "按下午 4 小时压缩，保留顺路、轻松、可拍照的点位，适合周末短出游。",
        "area": "西湖 · 灵隐 · 河坊街",
        "route": {"name": "西湖松弛打卡线", "distance_km": 14, "duration_min": 187, "mode": "walking"},
        "stops": [
            {"name": "白堤 / 孤山", "tag": "湖景", "duration": "45min", "note": "先走湖边视野最开阔的一段，适合拍照开场。", "x": 60, "y": 24},
            {"name": "灵隐寺文创街区", "tag": "文创", "duration": "55min", "note": "不硬排寺内长队，优先文创店和周边小逛。", "x": 22, "y": 66},
            {"name": "河坊街 / 南宋御街", "tag": "茶食", "duration": "70min", "note": "收尾安排茶饮和小吃，离开时更好叫车。", "x": 84, "y": 50},
        ],
        "activities": [
            {"name": "灵隐寺文创店", "tags": ["文创", "可预约"], "rating": 4.7, "price": "¥38/人", "note": "适合买伴手礼，排队超过 15 分钟就跳过。"},
            {"name": "河坊街龙井茶舍", "tags": ["茶饮", "休闲放松"], "rating": 4.5, "price": "¥48/人", "note": "适合作为中途恢复点，避开正餐排队。"},
            {"name": "西湖日落点", "tags": ["拍照", "免费"], "rating": 4.8, "price": "免费", "note": "晴天优先保留，雨天改去室内文创店。"},
        ],
    },
    "上海": {
        "title": "上海梧桐区周末 Citywalk",
        "summary": "把武康路、安福路和永康路串成一条低压力短线，适合朋友小聚和拍照。",
        "area": "徐汇 · 衡复风貌区",
        "route": {"name": "梧桐树咖啡散步线", "distance_km": 6.8, "duration_min": 150, "mode": "walking"},
        "stops": [
            {"name": "武康大楼", "tag": "地标", "duration": "30min", "note": "先拍建筑外观，避开正午逆光。", "x": 22, "y": 35},
            {"name": "安福路", "tag": "咖啡", "duration": "55min", "note": "店铺密集，适合灵活替换。", "x": 48, "y": 55},
            {"name": "永康路", "tag": "夜场", "duration": "60min", "note": "晚一点更有氛围，结束后地铁/打车都方便。", "x": 78, "y": 44},
        ],
        "activities": [
            {"name": "安福路咖啡窗口", "tags": ["咖啡", "拍照"], "rating": 4.6, "price": "¥35/人", "note": "排队长就换隔壁同类型店。"},
            {"name": "武康路买手店", "tags": ["逛店", "小众"], "rating": 4.4, "price": "按需", "note": "适合 i 人慢逛，社交压力低。"},
            {"name": "永康路轻食酒馆", "tags": ["朋友聚会", "可续摊"], "rating": 4.5, "price": "¥98/人", "note": "作为后续点，适合临时加时。"},
        ],
    },
    "北京": {
        "title": "北京胡同文化半日线",
        "summary": "围绕什刹海和鼓楼压缩成顺路路线，兼顾打卡、咖啡和晚间小吃。",
        "area": "什刹海 · 鼓楼 · 南锣鼓巷",
        "route": {"name": "胡同慢行线", "distance_km": 7.2, "duration_min": 165, "mode": "walking"},
        "stops": [
            {"name": "什刹海", "tag": "湖景", "duration": "45min", "note": "先走水边，体感更舒服。", "x": 25, "y": 58},
            {"name": "鼓楼", "tag": "地标", "duration": "40min", "note": "拍照点集中，避免在窄路久停。", "x": 55, "y": 32},
            {"name": "南锣鼓巷", "tag": "小吃", "duration": "65min", "note": "人多时只走支巷，减少排队。", "x": 78, "y": 54},
        ],
        "activities": [
            {"name": "鼓楼咖啡小店", "tags": ["咖啡", "休息"], "rating": 4.5, "price": "¥42/人", "note": "适合作为中段补给。"},
            {"name": "胡同文创店", "tags": ["文创", "伴手礼"], "rating": 4.4, "price": "¥30/人", "note": "动线短，不耽误主路线。"},
            {"name": "南锣支巷小吃", "tags": ["小吃", "平价"], "rating": 4.3, "price": "¥45/人", "note": "排队超过 20 分钟就换备选。"},
        ],
    },
    "新加坡": {
        "title": "新加坡滨海半日线",
        "summary": "把滨海湾、哈芝巷和夜景串起来，适合短时间高密度打卡。",
        "area": "Marina Bay · Haji Lane",
        "route": {"name": "滨海夜景打卡线", "distance_km": 8.5, "duration_min": 175, "mode": "walking"},
        "stops": [
            {"name": "滨海湾花园", "tag": "地标", "duration": "60min", "note": "先完成核心打卡，雨天可进室内温室。", "x": 67, "y": 30},
            {"name": "鱼尾狮公园", "tag": "拍照", "duration": "35min", "note": "傍晚光线更稳。", "x": 48, "y": 52},
            {"name": "哈芝巷", "tag": "街区", "duration": "65min", "note": "适合吃饭和买小物，结束后交通方便。", "x": 22, "y": 68},
        ],
        "activities": [
            {"name": "Supertree 灯光秀", "tags": ["夜景", "免费"], "rating": 4.8, "price": "免费", "note": "按场次倒推路线时间。"},
            {"name": "Haji Lane 轻食店", "tags": ["聚会", "拍照"], "rating": 4.5, "price": "S$18/人", "note": "人多时可转 Arab Street。"},
            {"name": "滨海湾室内备选", "tags": ["雨天", "亲子"], "rating": 4.6, "price": "按票价", "note": "天气异常时替代户外段。"},
        ],
    },
}

def _infer_weekend_city(text: str, city_hint: str = "") -> str:
    s = str(text or "")
    for city in WEEKEND_CITY_PLANS:
        if city in s:
            return city
    return (city_hint or "杭州").replace("市", "").strip() or "杭州"

def _pick_weekend_template(city: str) -> dict:
    c = (city or "").replace("市", "").strip()
    if c in WEEKEND_CITY_PLANS:
        return WEEKEND_CITY_PLANS[c]
    return {
        "title": f"{c or '本地'}周末半日出行线",
        "summary": "使用本地出行知识生成顺路方案，实时服务波动时也能稳定交付。",
        "area": f"{c or '本地'}热门街区",
        "route": {"name": "轻量打卡线", "distance_km": 6.5, "duration_min": 150, "mode": "walking"},
        "stops": [
            {"name": f"{c}热门地标", "tag": "打卡", "duration": "45min", "note": "先完成最有代表性的点位。", "x": 24, "y": 48},
            {"name": f"{c}特色街区", "tag": "逛店", "duration": "55min", "note": "安排咖啡、文创或小吃作为缓冲。", "x": 52, "y": 34},
            {"name": f"{c}夜景/商圈", "tag": "收尾", "duration": "60min", "note": "最后放在交通更方便的位置。", "x": 78, "y": 62},
        ],
        "activities": [
            {"name": f"{c}文创小店", "tags": ["文创", "可替换"], "rating": 4.4, "price": "¥40/人", "note": "适合作为低风险休息点。"},
            {"name": f"{c}本地茶饮", "tags": ["补给", "平价"], "rating": 4.3, "price": "¥28/人", "note": "用于应对排队或天气变化。"},
            {"name": f"{c}夜景点", "tags": ["拍照", "免费"], "rating": 4.6, "price": "免费", "note": "作为行程收尾更自然。"},
        ],
    }

def _detect_map_provider(text: str, default: str = "gaode") -> str:
    s = str(text or "").lower()
    if "google" in s or "谷歌" in s:
        return "google"
    if "百度" in s or "baidu" in s:
        return "baidu"
    if "高德" in s or "gaode" in s or "amap" in s:
        return "gaode"
    return default if default in ("baidu", "gaode", "google") else "gaode"

def _time_slots(prompt: str, count: int) -> list:
    s = str(prompt or "")
    if "晚上" in s or "夜" in s:
        base = ["18:30", "19:30", "20:30", "21:20"]
    elif "上午" in s or "早上" in s:
        base = ["09:30", "10:30", "11:30", "12:20"]
    else:
        base = ["14:00", "15:10", "16:30", "17:40"]
    return (base + [base[-1]])[:count]

def _weekend_map_urls(city: str, stops: list) -> dict:
    first = stops[0]["name"] if stops else city
    last = stops[-1]["name"] if stops else city
    query = quote(f"{city} {' '.join([s.get('name','') for s in stops])}")
    origin = quote(f"{city}{first}")
    destination = quote(f"{city}{last}")
    return {
        "baidu": f"https://map.baidu.com/dir/?origin=name:{origin}&destination=name:{destination}&mode=walking&output=html",
        "gaode": f"https://www.amap.com/dir?from[name]={origin}&to[name]={destination}&type=walk",
        "google": f"https://www.google.com/maps/search/{query}",
    }

def _calibrate_weekend_pois(city: str, stops: list) -> tuple[list, bool]:
    calibrated = []
    ok_count = 0
    for stop in stops:
        s = dict(stop)
        query = f"{city}{s.get('name','')}"
        poi = None
        matches = search_baidu_place(query, city, 1)
        if matches:
            poi = matches[0]
            loc = poi.get("location") or {}
            s["name"] = poi.get("name") or s.get("name")
            s["address"] = poi.get("address") or ""
            s["lat"] = loc.get("lat")
            s["lng"] = loc.get("lng")
            s["poi_source"] = "baidu_place"
        if not s.get("lat") or not s.get("lng"):
            loc = geocode_baidu(query, city)
            if loc:
                s.update(loc)
                s["poi_source"] = "baidu_geocode"
        if s.get("lat") and s.get("lng"):
            ok_count += 1
        calibrated.append(s)
    return calibrated, ok_count >= 2

def _baidu_walking_between(start: dict, end: dict) -> Optional[dict]:
    if not all([start.get("lat"), start.get("lng"), end.get("lat"), end.get("lng")]):
        return None
    try:
        r = requests.get(BAIDU_WALKING_URL, params={
            "origin": f"{start['lat']},{start['lng']}",
            "destination": f"{end['lat']},{end['lng']}",
            "ak": BAIDU_AK
        }, timeout=REQUEST_TIMEOUT)
        d = r.json()
        if d.get("status") != 0:
            return None
        best = d.get("result", {}).get("routes", [{}])[0]
        points = []
        for step in best.get("steps", [])[:20]:
            path = step.get("path") or ""
            if isinstance(path, str) and path:
                for pair in path.split(";"):
                    try:
                        lng, lat = pair.split(",")[:2]
                        points.append({"lng": float(lng), "lat": float(lat)})
                    except Exception:
                        pass
            for key in ("start_location", "end_location"):
                loc = step.get(key) or {}
                if loc.get("lng") and loc.get("lat"):
                    points.append({"lng": loc.get("lng"), "lat": loc.get("lat")})
        return {
            "distance_m": int(best.get("distance", 0) or 0),
            "duration_sec": int(best.get("duration", 0) or 0),
            "steps": best.get("steps", [])[:8],
            "points": points,
        }
    except Exception as e:
        print(f"[baidu_walk]{_safe_error_text(e)}")
    return None

def _calibrate_weekend_route(route: dict, stops: list) -> tuple[dict, list]:
    real_segments = []
    distance_m = 0
    duration_sec = 0
    if len(stops) >= 2:
        route_points = []
        for a, b in zip(stops, stops[1:]):
            seg = _baidu_walking_between(a, b)
            if not seg:
                real_segments = []
                break
            real_segments.append({
                "from": a.get("name", ""),
                "to": b.get("name", ""),
                "distance_m": seg["distance_m"],
                "duration_sec": seg["duration_sec"],
            })
            distance_m += seg["distance_m"]
            duration_sec += seg["duration_sec"]
            route_points.extend(seg.get("points") or [])
    out = dict(route)
    if real_segments and distance_m > 0:
        out.update({
            "distance_m": distance_m,
            "distance_km": round(distance_m / 1000, 1),
            "duration_sec": duration_sec,
            "duration_min": max(1, round(duration_sec / 60)),
            "source": "baidu_walking",
            "calibrated": True,
            "points": route_points,
        })
    else:
        out.update({
            "distance_m": round(float(out.get("distance_km", 0)) * 1000),
            "duration_sec": int(out.get("duration_min", 0)) * 60,
            "source": "curated_backup",
            "calibrated": False,
        })
    return out, real_segments

def _mock_queue_status(activity: dict, idx: int, persona: str) -> dict:
    keys = _persona_keys(persona)
    queue = [8, 14, 6, 18][idx % 4]
    if "social_fear" in keys:
        queue = max(3, queue - 5)
    if "special_force" in keys:
        queue = max(2, queue - 3)
    status = "可预约" if idx != 2 else "现场取号"
    return {
        "queue_time": f"约{queue}分钟",
        "booking_status": status,
        "persona_reason": "低排队、低社交压力" if "social_fear" in keys else "顺路且适合半日节奏",
    }

def _activity_mock_image(idx: int) -> str:
    palettes = [
        "linear-gradient(135deg,#e9d1a5,#d8f0c8)",
        "linear-gradient(135deg,#b9ddb7,#f2f1c9)",
        "linear-gradient(135deg,#bdddf2,#fff0c2)",
    ]
    return palettes[idx % len(palettes)]

def _enrich_weekend_activities(city: str, activities: list, persona: str) -> list:
    enriched = []
    for i, item in enumerate(activities):
        a = dict(item)
        query = a.get("name") or " ".join(a.get("tags", [])) or "餐厅"
        real = tool_call_meituan_skill(
            intent="nearby_search", city=city, keyword=query,
            filters={"sort_by": "distance"}, limit=1
        )
        if real.get("success") and real.get("results"):
            p = real["results"][0]
            a["name"] = p.get("name") or a.get("name")
            a["address"] = p.get("address") or ""
            a["rating"] = p.get("rating") or a.get("rating")
            if p.get("cost"):
                a["price"] = f"¥{p.get('cost')}/人"
            a["merchant_source"] = p.get("source") or real.get("source")
            if p.get("photo_url"):
                a["image_url"] = p["photo_url"]
        a.update(_mock_queue_status(a, i, persona))
        a["image_style"] = _activity_mock_image(i)
        enriched.append(a)
    return enriched

def _looks_weekend_trip(text: str) -> bool:
    return bool(re.search(r"周末|半日|下午|上午|晚上|citywalk|Citywalk|CITYWALK|周边游|打卡|活动|行程|出游|游玩|把事情做完", str(text or "")))

def tool_plan_weekend_trip(city: str, user_prompt: str,
                           persona: str = "", route_profile: str = "",
                           map_provider: str = "", duration_hours: float = 4) -> dict:
    city = _infer_weekend_city(user_prompt, city)
    tmpl = _pick_weekend_template(city)
    rp = _resolve_route_profile(route_profile, persona)
    provider = _detect_map_provider(user_prompt, map_provider or "gaode")
    compact = duration_hours and float(duration_hours) <= 4
    stops = [dict(s) for s in tmpl["stops"][:3 if compact else len(tmpl["stops"])]]
    stops, poi_calibrated = _calibrate_weekend_pois(city, stops)
    times = _time_slots(user_prompt, len(stops))
    for i, stop in enumerate(stops):
        stop["order"] = i + 1
        stop["time"] = times[i]
    activities = _enrich_weekend_activities(
        city, [dict(a) for a in tmpl["activities"][:3 if compact else len(tmpl["activities"])]], persona
    )
    route = dict(tmpl["route"])
    if rp == "fast":
        route["duration_min"] = max(45, round(route["duration_min"] * 0.82))
        route["name"] = "高效率压缩线"
    elif rp == "quiet":
        route["name"] = "低人流安静线"
    elif rp == "budget":
        route["name"] = "低预算高性价比线"
    elif rp == "scenic":
        route["name"] = tmpl["route"]["name"]
    route, route_segments = _calibrate_weekend_route(route, stops)
    map_urls = _weekend_map_urls(city, stops)
    map_data = _build_map_data(
        stops[-1] if stops else {},
        route.get("points") or stops,
        [
            {"category": "stop", "items": stops},
            {"category": "activity", "items": _attach_item_coords(activities, city)},
        ],
    )
    status_flow = [
        f"正在识别{city}周末半日游需求",
        "正在匹配热门地标路线",
        "正在筛选文创小店与茶饮补给",
        "行程已生成，可直接导航",
    ]
    return {
        "success": True,
        "type": "weekend_plan",
        "city": city,
        "title": tmpl["title"],
        "summary": tmpl["summary"],
        "area": tmpl["area"],
        "persona": persona or "",
        "persona_label": PERSONA_LABELS.get((persona or "").strip().lower(), ""),
        "route_profile": rp,
        "route_profile_meta": _route_profile_meta(rp, int(route["duration_min"])),
        "map_provider": provider,
        "primary_map_url": map_urls.get(provider),
        "map_urls": map_urls,
        "status_flow": status_flow,
        "route": route,
        "map_data": map_data,
        "route_segments": route_segments,
        "stops": stops,
        "activities": activities,
        "risks": [
            {"level": "warn", "text": "任一点排队超过 20 分钟，直接切换到同街区备选店，保证半日节奏。"},
            {"level": "info", "text": "如遇商家排队过长，自动切换同街区备选，不打断你的出行节奏。"},
            {"level": "ok", "text": "终点安排在商圈/主路附近，方便打车、地铁或继续吃饭。"},
        ],
        "innovation": ["人格路线画像", "排队超时自动改道", "真实路线校准", "打卡 + 餐饮 + 后续一体化"],
        "data_layer": {
            "route": "baidu_walking" if route.get("calibrated") else "smart_backup",
            "poi": "baidu_place" if poi_calibrated else "smart_backup",
            "merchant": "meituan_or_gaode" if any(a.get("merchant_source") for a in activities) else "smart_backup",
            "queue_and_booking": "agent_prediction",
        },
        "fallback_ready": True,
    }

# ══ 核心工具 ══
def tool_get_weather(city: str) -> dict:
    ck=city.replace("市","").replace("省","").strip()
    known = CITY_GEO_INDEX.get(_city_alias(ck))
    loc = {"lat":known["lat"],"lng":known["lng"],"name":known["name"],"country":known["country"]} if known else None
    if not loc:
        loc=geocode_openmeteo(ck)
    if not loc:
        c=geocode_baidu(ck)
        if c: loc={"lat":c["lat"],"lng":c["lng"],"name":ck,"country":"中国"}
    if not loc: return {"success":False,"error":f"找不到城市：{ck}"}
    try:
        r=requests.get(OM_WEATHER_URL,params={
            "latitude":loc["lat"],"longitude":loc["lng"],
            "current":"temperature_2m,apparent_temperature,weather_code,wind_speed_10m,wind_direction_10m,relative_humidity_2m",
            "timezone":"auto","forecast_days":1},timeout=REQUEST_TIMEOUT)
        r.raise_for_status()
        curr=r.json().get("current",{})
        wcode=int(curr.get("weather_code",0))
        temp=round(float(curr.get("temperature_2m",20)))
        feels=round(float(curr.get("apparent_temperature",temp)))
        rh=round(float(curr.get("relative_humidity_2m",50)))
        cd=loc["name"]
        if loc.get("country") and loc["country"] not in ("中国",):
            cd=f"{loc['name']}({loc['country']})"
        return {"success":True,"city":cd,"data":{
            "text":WMO_ZH.get(wcode,"未知"),"temp":temp,"feels_like":feels,
            "wind_dir":_deg_to_dir(curr.get("wind_direction_10m",0)),
            "wind_class":_kmh_to_level(curr.get("wind_speed_10m",0)),"rh":rh}}
    except Exception as e: return {"success":False,"error":_safe_error_text(e)}


def tool_plan_route(city: str, start: str, destination: str,
                    riding_type: int = 0, road_prefer: Optional[int] = None,
                    route_profile: str = "", persona: str = "",
                    route_strategy: str = "") -> dict:
    rp = _resolve_route_profile(route_profile, persona)
    profile_cfg = ROUTE_PROFILES[rp]
    road_prefer = profile_cfg["road_prefer"] if road_prefer is None else int(road_prefer)
    sn=start or f"{city}人民广场"
    start_coord = _parse_lat_lng(sn)
    oc=start_coord or geocode_baidu(sn,city)
    start_name = "当前位置" if start_coord else sn
    dc=geocode_baidu(destination,city)
    if not oc: return {"success":False,"error":f"起点解析失败：{sn}"}
    if not dc: return {"success":False,"error":f"终点解析失败：{destination}"}
    try:
        r=requests.get(BAIDU_RIDING_URL,params={
            "origin":f"{oc['lat']},{oc['lng']}","destination":f"{dc['lat']},{dc['lng']}",
            "riding_type":riding_type,"road_prefer":road_prefer,
            "steps_info":1,"ret_coordtype":"bd09ll","ak":BAIDU_AK},timeout=REQUEST_TIMEOUT)
        d=r.json()
    except Exception as e: return {"success":False,"error":_safe_error_text(e)}
    if d.get("status")!=0: return {"success":False,"error":d.get("message","路线规划失败")}
    res=d["result"]; best=res["routes"][0]
    raw_steps = best.get("steps", [])
    steps=[{"name":s.get("name","无名路"),"instruction":s.get("instruction",""),
            "turn_type":s.get("turn_type",""),"distance":s.get("distance",0),
            "duration":s.get("duration",0),"start_location":s.get("start_location",{}),
            "end_location":s.get("end_location",{}),"path":s.get("path","")} for s in raw_steps]
    route_points = _extract_baidu_path_points(raw_steps)
    if not route_points:
        route_points = [{"lat": oc.get("lat"), "lng": oc.get("lng")}, {"lat": dc.get("lat"), "lng": dc.get("lng")}]
    duration_min = round(best["duration"]/60)
    route_profile_meta = _route_profile_meta(rp, duration_min)
    route_profile_meta["duration_min"] = duration_min
    start_obj = {"name":start_name,"lat":res.get("origin",{}).get("lat"),"lng":res.get("origin",{}).get("lng")}
    dest_obj = {"name":destination,"lat":res.get("destination",{}).get("lat"),"lng":res.get("destination",{}).get("lng")}
    return {"success":True,
        "mode": "riding",
        "persona": persona or "",
        "persona_label": PERSONA_LABELS.get((persona or "").strip().lower(), ""),
        "route_profile": rp,
        "route_profile_meta": route_profile_meta,
        "route_profiles": _build_route_profiles(duration_min, rp),
        "route_strategy": route_strategy or profile_cfg["strategy"],
        "road_prefer": road_prefer,
        "riding_type": riding_type,
        "start":start_obj,
        "destination":dest_obj,
        "map_data": _build_map_data(dest_obj, route_points, [
            {"category": "start", "items": [start_obj]},
            {"category": "destination", "items": [dest_obj]},
        ]),
        "route":{"distance_m":best["distance"],"distance_km":round(best["distance"]/1000,2),
                 "duration_sec":best["duration"],"duration_min":duration_min,"steps":steps,
                 "points": route_points}}


_CITY_MAP = {
    "新加坡":"Singapore","上海":"Shanghai","北京":"Beijing","香港":"Hong Kong",
    "东京":"Tokyo","首尔":"Seoul","纽约":"New York","巴黎":"Paris",
    "伦敦":"London","曼谷":"Bangkok","台北":"Taipei","澳门":"Macau",
    "广州":"Guangzhou","成都":"Chengdu","深圳":"Shenzhen","大阪":"Osaka",
    "京都":"Kyoto","米兰":"Milan","罗马":"Rome","巴塞罗那":"Barcelona",
}
_KW_MAP = {
    "米其林":"Michelin","餐厅":"restaurant","一星":"one star","二星":"two star",
    "三星":"three star","摘星":"Michelin star","法餐":"French cuisine",
    "日料":"Japanese cuisine","中餐":"Chinese cuisine","意餐":"Italian cuisine",
    "推荐":"recommended","最好":"best","附近":"near","高端":"fine dining",
}

def _enhance_query(q: str) -> str:
    enhanced = q
    for zh, en in {**_CITY_MAP, **_KW_MAP}.items():
        if zh in q:
            enhanced += f" {en}"
    return enhanced

def _michelin_csv_fallback(query: str, limit: int = 5,
                           rag_error: str = "") -> dict:
    if not os.path.exists(CSV_PATH):
        return {"success":False,"error":"米其林RAG和本地CSV均不可用"}
    q_full = _enhance_query(query)
    terms = [t.lower() for t in re.split(r"[\s,，。/|]+", q_full) if len(t.strip()) >= 2]
    city_filters = []
    for zh, en in _CITY_MAP.items():
        if zh in query or en.lower() in q_full.lower():
            city_filters.extend([zh.lower(), en.lower()])
    required_star = None
    if "三星" in query or "three star" in q_full.lower():
        required_star = 3
        terms.extend(["3 stars", "3 star"])
    if "二星" in query or "two star" in q_full.lower():
        required_star = 2
        terms.extend(["2 stars", "2 star"])
    if "一星" in query or "one star" in q_full.lower():
        required_star = 1
        terms.extend(["1 star", "1 star"])
    scored = []
    try:
        with open(CSV_PATH, "r", encoding="utf-8") as f:
            for row in csv.DictReader(f):
                location_hay = (row.get("location","") or "").lower()
                blob = " ".join([
                    row.get("name",""), row.get("location",""), row.get("address",""),
                    row.get("cuisine",""), row.get("award",""), row.get("country",""),
                    row.get("star_rating",""), row.get("content","")
                ]).lower()
                if city_filters and not any(c in location_hay for c in city_filters):
                    continue
                if required_star is not None:
                    try:
                        if int(float(row.get("star_rating") or 0)) != required_star:
                            continue
                    except Exception:
                        continue
                score = 0
                for t in terms:
                    if t and t in blob:
                        score += 3
                if "米其林" in query or "michelin" in q_full.lower():
                    score += 1
                try:
                    score += int(float(row.get("star_rating") or 0))
                except Exception:
                    pass
                if score > 0:
                    scored.append((score, row))
        scored.sort(key=lambda x: x[0], reverse=True)
        rows = [r for _, r in scored[:limit]]
    except Exception as e:
        return {"success":False,"error":f"本地米其林CSV检索失败：{e}"}
    if not rows:
        return {
            "success": True,
            "answer": "本地米其林数据里没有检索到足够匹配的餐厅，请换一个城市、菜系或星级关键词再试。",
            "references": ["rag_documents.csv"],
            "fallback": True,
            "rag_error": rag_error,
        }
    lines = ["已用本地米其林数据完成检索："]
    refs = []
    for i, row in enumerate(rows, 1):
        star = row.get("star_rating") or "0"
        award = row.get("award") or f"{star} star"
        lines.append(
            f"{i}. {row.get('name','')}｜{row.get('location','')}｜{award}｜"
            f"{row.get('cuisine','')}｜{row.get('address','')}｜{row.get('price','')}"
        )
        refs.append(str(row.get("doc_id") or row.get("url") or "rag_documents.csv"))
    if rag_error:
        lines.append("说明：向量RAG暂时不可用，已自动切换本地CSV检索，演示结果不断线。")
    return {
        "success": True,
        "answer": _clean_markdown("\n".join(lines)),
        "references": refs,
        "fallback": True,
        "rag_error": rag_error,
    }


def tool_search_michelin(query: str) -> dict:
    if not MICHELIN_AVAILABLE:
        return _michelin_csv_fallback(query, rag_error=MICHELIN_IMPORT_ERROR or "米其林RAG模块未加载")
    try:
        result = ask_michelin(_enhance_query(query))
        return {"success":True,"answer":_clean_markdown(result["answer"]),"references":result["references"]}
    except Exception as e:
        return _michelin_csv_fallback(query, rag_error=_safe_error_text(e))


# ══ 新增：最近米其林餐厅（地理索引）══
def _haversine(lat1: float, lng1: float, lat2: float, lng2: float) -> float:
    """计算两坐标间距离（km）"""
    R = 6371.0
    φ1, φ2 = math.radians(lat1), math.radians(lat2)
    dφ = math.radians(lat2 - lat1)
    dλ = math.radians(lng2 - lng1)
    a = math.sin(dφ/2)**2 + math.cos(φ1)*math.cos(φ2)*math.sin(dλ/2)**2
    return R * 2 * math.atan2(math.sqrt(a), math.sqrt(1-a))


def tool_find_nearest_michelin(lat: float, lng: float,
                                limit: int = 5,
                                cuisine_filter: str = "") -> dict:
    """根据用户坐标查找最近的米其林餐厅"""
    if pd is None:
        return {"success":False,"error":"缺少 pandas，请先安装 pandas 后使用最近米其林地理排序"}
    try:
        df = pd.read_csv(CSV_PATH)
        # 保留有坐标的行
        df = df.dropna(subset=["latitude","longitude"])
        df["latitude"]  = pd.to_numeric(df["latitude"],  errors="coerce")
        df["longitude"] = pd.to_numeric(df["longitude"], errors="coerce")
        df = df.dropna(subset=["latitude","longitude"])

        if cuisine_filter:
            mask = df["cuisine"].str.contains(cuisine_filter, case=False, na=False)
            df_filtered = df[mask]
            if len(df_filtered) > 0:
                df = df_filtered

        df = df.copy()
        df["distance_km"] = df.apply(
            lambda r: _haversine(lat, lng, r["latitude"], r["longitude"]), axis=1
        )
        nearest = df.nsmallest(limit, "distance_km")

        restaurants = []
        for _, row in nearest.iterrows():
            restaurants.append({
                "name":        str(row.get("name", "")),
                "address":     str(row.get("address", "")),
                "cuisine":     str(row.get("cuisine", "")),
                "star_rating": str(row.get("star_rating", "")),
                "award":       str(row.get("award", "")),
                "price":       str(row.get("price", "")),
                "distance_km": round(float(row["distance_km"]), 2),
                "latitude":    float(row["latitude"]),
                "longitude":   float(row["longitude"]),
            })
        return {"success":True, "restaurants":restaurants, "user_lat":lat, "user_lng":lng}
    except Exception as e:
        return {"success":False,"error":_safe_error_text(e)}


# ✅ 美团 Skill 工具实现（真实美团数据：开放平台 → 本地 mttravel Skill）
def tool_call_meituan_skill(intent: str, city: str = "",
                             keyword: str = "", location: str = "",
                             user_lat: float = None, user_lng: float = None,
                             filters: dict = None, limit: int = 5) -> dict:
    """
    美团生活服务工具（只返回真实美团数据）
    Layer1: 美团开放平台 API（有 MEITUAN_API_KEY 时）
    Layer2: 本地美团 Travel Skill CLI（mttravel）
    无真实美团返回时 success=false，绝不伪造店名。
    替换数据源只需修改此函数，Agent 工具接口不变。
    """
    filters  = filters or {}
    city = _guard_city_name(city)
    if city and user_lat and user_lng and not is_coord_near_city(user_lat, user_lng, city):
        print(f"⚠️ 坐标与城市冲突：city={city}, lat={user_lat}, lng={user_lng}，已忽略坐标")
        user_lat = None
        user_lng = None
    if user_lat and user_lng and (CITY_GEO_INDEX.get((city or "").replace("市", "")) or {}).get("country") in ("中国",):
        filters = dict(filters)
        filters["location_hint"] = f"纬度{float(user_lat):.6f},经度{float(user_lng):.6f}"
    MEITUAN_API_KEY = os.environ.get("MEITUAN_API_KEY", "")

    # ── 构造统一搜索关键词 ──
    intent_kw = {
        "restaurant_search": "餐厅", "hotel_search": "酒店",
        "ticket_search": "景点 门票", "group_buy_query": "团购 优惠",
        "nearby_search": "美食", "booking_query": "餐厅",
    }
    search_kw = keyword or filters.get("cuisine", "") or intent_kw.get(intent, "餐厅")
    tags = filters.get("tags", [])
    if isinstance(tags, list) and tags:
        search_kw = " ".join(tags[:2]) + " " + search_kw
    skill_route = _pick_meituan_skill(intent, search_kw)

    if skill_route == "coupon":
        return _apply_city_guard_to_result(_call_meituan_coupon_skill(intent, city, search_kw, limit), city)
    if skill_route == "paotui":
        return _apply_city_guard_to_result(_call_meituan_paotui_skill(intent, city, search_kw, user_lat, user_lng, limit), city)
    if skill_route == "venue":
        venue_result = _call_meituan_venue_skill(intent, city, search_kw, limit)
        if venue_result.get("success"):
            return _apply_city_guard_to_result(venue_result, city)
        cli_fallback = _call_meituan_travel_cli(intent, city, search_kw, filters, limit)
        if cli_fallback.get("success"):
            cli_fallback["detail"] = "venue skill unavailable; used mttravel skill"
            return _apply_city_guard_to_result(cli_fallback, city)
        return venue_result

    # ══ Layer1：美团开放平台（需在 open.meituan.com 申请） ══
    if MEITUAN_API_KEY:
        try:
            import hashlib, time
            ts  = str(int(time.time()))
            sig = hashlib.md5(f"{MEITUAN_API_KEY}{ts}".encode()).hexdigest()
            params = {
                "app_key":   MEITUAN_API_KEY,
                "timestamp": ts,
                "sign":      sig,
                "city_name": city,
                "keyword":   search_kw,
                "page_size": min(limit, 20),
                "lat":       user_lat or "",
                "lng":       user_lng or "",
            }
            r = requests.get(
                "https://open-api.dianping.com/rest/openapi/service/life/pois",
                params=params, timeout=REQUEST_TIMEOUT
            )
            r.raise_for_status()
            data = r.json()
            if data.get("code") == 0:
                pois = data.get("data", {}).get("pois", [])
                results = [{
                    "name":     p.get("name",""),
                    "address":  p.get("address",""),
                    "rating":   p.get("avgScore",""),
                    "cost":     p.get("avgPrice",""),
                    "distance": p.get("distance",""),
                    "type":     p.get("frontCategoryName",""),
                    "tel":      p.get("phone",""),
                    "location": f"{p.get('lng','')},{p.get('lat','')}",
                    "photo_url": p.get("frontImg","") or p.get("photoUrl",""),
                    "source":   "meituan_skill",
                    "is_real_meituan": True,
                } for p in pois[:limit]]
                return _apply_city_guard_to_result({"success":True,"intent":intent,"city":city,
                        "keyword":search_kw,"count":len(results),
                        "results":results,"source":"meituan_skill",
                        "is_real_meituan": True}, city)
        except Exception as e:
            print(f"[meituan_api] {_safe_error_text(e)}，降级到本地美团 Skill")

    # ══ Layer2：本地美团 Travel Skill CLI（mttravel） ══
    cli_result = _call_meituan_travel_cli(intent, city, search_kw, filters, limit)
    if cli_result.get("success"):
        return _apply_city_guard_to_result(cli_result, city)

    return {
        "success": False,
        "intent": intent,
        "city": city,
        "keyword": search_kw,
        "source": "meituan_skill",
        "is_real_meituan": False,
        "error": MEITUAN_SKILL_UNAVAILABLE,
        "detail": cli_result.get("detail", ""),
        "recovery": {
            "message": "🍊 已从米其林知识库、百度地图等多源精选推荐。",
            "fallbacks": ["米其林知识库", "百度地图"],
        },
    }


def _tool_summary(fn: str, args: dict, result: dict) -> str:
    if not result.get("success"): return f"❌ {result.get('message') or result.get('error','失败')}"
    if fn=="get_weather":
        d=result.get("data",{})
        return f"{result.get('city','')} · {d.get('text','')} · {d.get('temp','')}℃ · {d.get('wind_dir','')}{d.get('wind_class','')} · 湿度{d.get('rh','')}%"
    if fn=="plan_route":
        r=result.get("route",{})
        meta=result.get("route_profile_meta",{})
        title=meta.get("title") or result.get("route_profile","")
        return f"{title}：{result.get('start',{}).get('name','')} → {result.get('destination',{}).get('name','')} · {r.get('distance_km','')}km · {r.get('duration_min','')}min"
    if fn=="plan_weekend_trip":
        r=result.get("route",{})
        return f"{result.get('city','')}周末方案：{result.get('title','')} · {r.get('distance_km','')}km · {r.get('duration_min','')}min · {len(result.get('stops',[]))}个点"
    if fn in ("plan_meituan_trip", "independent_trip_planner"):
        if not result.get("success", True):
            return f"❌ {result.get('error','失败')}"
        req=result.get("requirements",{})
        budget=result.get("budget",{})
        if result.get("commerce_mode") == "none":
            return f"{req.get('destination','')} · {req.get('days','')}天 · 预算{budget.get('total','')}元 · 独立行程规划"
        label = "兜底资源" if result.get("fallback_used") else "美团资源"
        return f"{req.get('destination','')} · {req.get('days','')}天 · 预算{budget.get('total','')}元 · {label}{len(result.get('hotels',[]))}家"
    if fn=="plan_panorama_trip":
        d=result.get("decision",{})
        return f"{result.get('origin',{}).get('name','')} → {result.get('destination',{}).get('name','')} · {d.get('label','')} · {result.get('distance_km','')}km · {d.get('priority','')}"
    if fn=="search_michelin":
        ans=_clean_markdown(result.get("answer",""))
        return ans[:100]+"…" if len(ans)>100 else ans
    if fn=="call_meituan_skill":
        if not result.get("success"): return f"❌ {result.get('error', result.get('message','失败'))}"
        if result.get("fallback") or result.get("source") == "mock_fallback":
            return f"美团 Skill 暂不可用，未展示店名：{result.get('city','')}{result.get('keyword','')}"
        count = result.get("count", 0)
        kw    = result.get("keyword", "")
        city  = result.get("city", "")
        tops  = result.get("results", [])[:2]
        names = "、".join([r["name"] for r in tops if r.get("name")])
        return f"🍴 {city}{kw}：找到{count}家，推荐：{names}"
    if fn=="find_nearest_michelin":
        rests=result.get("restaurants",[])
        if not rests: return "未找到附近餐厅"
        top=rests[0]
        return f"最近：{top['name']} · {top['distance_km']}km · {top['star_rating']}星"
    if fn=="mock_request_ride":
        q=result.get("quote",{})
        return f"打车待确认：{q.get('origin','')} → {q.get('destination','')} · {q.get('eta_minutes','-')}min · ¥{q.get('price_estimate','-')}"
    if fn=="mock_search_flights":
        rec=result.get("recommended",{})
        return f"航班待确认：{rec.get('airline','')} {rec.get('flight_id','')} · {rec.get('depart_time','')} · ¥{rec.get('price','-')}"
    if fn=="mock_start_service_monitor":
        mon=result.get("monitor",{})
        latest=mon.get("latest",{})
        return f"后台监控：{mon.get('target_name','')} · {latest.get('message','已启动')} · {latest.get('recommended_action','继续监控')}"
    if fn=="mock_get_monitor_status":
        mon=result.get("monitor",{})
        latest=mon.get("latest",{})
        return f"监控状态：{mon.get('monitor_id','')} · {mon.get('status','')} · {latest.get('message','')}"
    if fn=="create_pending_order":
        order = result.get("order", {})
        item = order.get("item", {})
        return f"待确认订单：{order.get('order_id','')} · {item.get('name','')} · 等待用户确认"
    if fn=="confirm_mock_order":
        return f"模拟下单：{result.get('order_id','')} · {result.get('status','')}"
    if fn=="simulate_price_scenario":
        env=result.get("current_env",{})
        best=result.get("best_window",{})
        return f"价格模拟：{env.get('event_label','')} · 当前¥{result.get('current_price','-')}(×{env.get('surge_factor','-')}) · 最优{best.get('label','')}¥{best.get('price','-')}"
    if fn=="patch_plan_item":
        return result.get("patch_summary","✅ 已更换")
    return "✅ 完成"


# ══ DeepSeek Agent 工具定义 ══
# ✅ 动态加载美团 Skill 工具定义
_MEITUAN_TOOLS = []
try:
    with open(os.path.join(BASE_DIR, "meituan_skill_tool.json"), "r", encoding="utf-8") as _f:
        _raw = json.load(_f)
        # 兼容两种格式：原始 function schema 或带 type:function 的格式
        for _item in _raw:
            if "type" not in _item:
                _MEITUAN_TOOLS.append({"type": "function", "function": _item})
            else:
                _MEITUAN_TOOLS.append(_item)
    print(f"✅ 已加载美团 Skill 工具：{[t['function']['name'] for t in _MEITUAN_TOOLS]}")
except FileNotFoundError:
    print("⚠️  meituan_skill_tool.json 未找到，美团工具不可用")
except Exception as _e:
    print(f"⚠️  美团工具加载失败：{_e}")

AGENT_TOOLS = [
    {"type":"function","function":{
        "name":"plan_meituan_trip",
        "description":(
            "行程规划路由工具。用户提到行程、几天、预算、酒店、住宿、美团、景点、旅游攻略时必须优先调用。"
            "必须提取目的地、天数、预算和美团使用偏好；不想用美团时走独立规划，明确美团交易/真实资源时才联动 Skill。"
        ),
        "parameters":{"type":"object","properties":{
            "city":{"type":"string","description":"当前城市或出发城市"},
            "user_prompt":{"type":"string","description":"用户原始需求"},
            "persona":{"type":"string","description":"relax/special/romantic/introvert/socialfear/student"},
            "map_provider":{"type":"string","enum":["baidu","gaode","google"],"description":"用户指定或当前优先地图"}},
            "required":["city","user_prompt"]}}},
    {"type":"function","function":{
        "name":"plan_panorama_trip",
        "description":(
            "全景出行规划工具。用户提到跨国、跨省、跨城、出差、飞机、高铁、机场、火车、从A到B的长距离路线、周末去外地时必须优先调用。"
            "先识别出发位置和目标目的地，再按地域层级与距离阈值选择飞机/高铁/自驾/地铁/打车/步行。"
            "只有用户明确说骑行、骑车、共享单车时，才把骑行作为路线方案。"
            "每次路线结果必须返回全景行程卡片：长途交通 + 到达城市市内接驳 + 短途备选；天气只作为辅助。"
        ),
        "parameters":{"type":"object","properties":{
            "city":{"type":"string","description":"当前城市或用户所在城市"},
            "user_prompt":{"type":"string","description":"用户原始需求"},
            "origin":{"type":"string","description":"出发地，可为空；为空时使用当前城市"},
            "destination":{"type":"string","description":"目标目的地"},
            "persona":{"type":"string","description":"relax/special/romantic/introvert/socialfear/student"},
            "map_provider":{"type":"string","enum":["baidu","gaode","google"],"description":"用户指定或当前优先地图"}},
            "required":["city","user_prompt"]}}},
    {"type":"function","function":{
        "name":"get_weather",
        "description":"查询全球任意城市实时天气。用户问天气必须调用。",
        "parameters":{"type":"object","properties":{"city":{"type":"string","description":"城市名，中英文均可"}},"required":["city"]}}},
    {"type":"function","function":{
        "name":"plan_weekend_trip",
        "description":(
            "规划周末/半日/citywalk/周边游/热门打卡综合出行任务。"
            "用户提到周末、半日、下午、citywalk、周边游、打卡、活动规划、把事情做完时必须调用。"
            "返回结构化路线、活动、地图链接、异常兜底和数据来源分层。"
        ),
        "parameters":{"type":"object","properties":{
            "city":{"type":"string","description":"城市名"},
            "user_prompt":{"type":"string","description":"用户原始需求"},
            "persona":{"type":"string","description":"relax/special/romantic/introvert/socialfear/student"},
            "route_profile":{"type":"string","enum":["fast","scenic","quiet","budget"]},
            "map_provider":{"type":"string","enum":["baidu","gaode","google"],"description":"用户指定或当前优先地图"},
            "duration_hours":{"type":"number","description":"可用时长，半日默认4小时","default":4}},
            "required":["city","user_prompt"]}}},
    {"type":"function","function":{
        "name":"plan_route",
        "description":"规划中国大陆城市间的骑行路线。必须根据用户人格和偏好选择 route_profile，不要固定单一路线。",
        "parameters":{"type":"object","properties":{
            "city":{"type":"string"},"start":{"type":"string","description":"起点地址。若用户提供当前位置坐标，可填 纬度xx,经度xx"},
            "destination":{"type":"string"},
            "riding_type":{"type":"integer","default":0},
            "road_prefer":{"type":"integer","description":"百度骑行偏好，0默认，3避逆行台阶"},
            "route_profile":{
                "type":"string",
                "enum":["fast","scenic","quiet","budget"],
                "description":"fast=最快，scenic=海边/风景慢骑，quiet=安静避人流，budget=省钱高性价比"
            },
            "persona":{"type":"string","description":"relax/special/romantic/introvert/socialfear/student"},
            "route_strategy":{"type":"string","description":"一句话说明为什么选择该路线画像"}},
            "required":["city","destination"]}}},
    {"type":"function","function":{
        "name":"search_michelin",
        "description":(
            "【必须调用】查询米其林餐厅知识库。"
            "用户提到米其林/餐厅/美食/一星/二星/三星/好吃/推荐吃/哪里吃/fine dining/restaurant 时必须调用。"
            "不得凭记忆回答，必须查库。"
        ),
        "parameters":{"type":"object","properties":{
            "query":{"type":"string","description":"查询内容，支持中英文"}},"required":["query"]}}},
    # ✅ 新增：最近米其林
    {"type":"function","function":{
        "name":"find_nearest_michelin",
        "description":(
            "根据用户当前GPS坐标查找最近的米其林餐厅，按距离排序返回。"
            "用户说「附近」「最近」「离我近」「我在哪里能吃」「我现在在XX」等，必须调用此工具。"
        ),
        "parameters":{"type":"object","properties":{
            "lat":{"type":"number","description":"用户纬度"},
            "lng":{"type":"number","description":"用户经度"},
            "limit":{"type":"integer","description":"返回数量，默认5","default":5},
            "cuisine_filter":{"type":"string","description":"可选菜系过滤，如Japanese、French","default":""}},
            "required":["lat","lng"]}}},
    {"type":"function","function":{
        "name":"mock_request_ride",
        "description":"生成打车/叫车/网约车/落地接驳的待确认订单。用于用户明确要叫车、打车、接驳，或排队低峰窗口需要提醒叫车时。只生成待确认订单，不真实支付。",
        "parameters":{"type":"object","properties":{
            "origin":{"type":"string","description":"上车点或当前位置"},
            "destination":{"type":"string","description":"下车点"},
            "city":{"type":"string","description":"所在城市"},
            "trigger_reason":{"type":"string","description":"为什么此时建议叫车，例如排队即将有位、赶飞机、雨天接驳"},
            "user_context":{"type":"object","description":"预算、人格、时间、行程上下文"}},
            "required":["destination"]}}},
    {"type":"function","function":{
        "name":"mock_search_flights",
        "description":"查询 mock 航班并生成机票待确认订单。用户说机票、航班、飞机票、订机票、买机票时必须调用。只生成待确认订单，不真实出票。",
        "parameters":{"type":"object","properties":{
            "origin":{"type":"string","description":"出发城市"},
            "destination":{"type":"string","description":"到达城市"},
            "date":{"type":"string","description":"出发日期，可为空"},
            "budget":{"type":"integer","description":"预算，可为空"},
            "passengers":{"type":"integer","description":"乘机人数，默认1"},
            "cabin":{"type":"string","description":"舱位，默认economy"},
            "user_context":{"type":"object","description":"预算、人格、时间、行程上下文"}},
            "required":["origin","destination"]}}},
    {"type":"function","function":{
        "name":"mock_start_service_monitor",
        "description":"启动后台资源监控，模拟餐厅排队、拍照点人流、有位/满座等状态变化。用户说排队、等位、有位、满座、人多、提醒我、后台盯时必须调用。",
        "parameters":{"type":"object","properties":{
            "resource_type":{"type":"string","description":"queue/crowd/seat/ride_window"},
            "target_name":{"type":"string","description":"被监控的餐厅、景点、拍照点或服务"},
            "city":{"type":"string","description":"城市"},
            "condition":{"type":"string","description":"触发条件，例如排队低于10分钟、有位、上午人少"},
            "callback_action":{"type":"string","description":"触发后建议动作，例如提醒叫车、切换路线"},
            "duration_minutes":{"type":"integer","description":"监控时长，默认30分钟"},
            "user_context":{"type":"object","description":"预算、人格、时间、行程上下文"}},
            "required":["target_name"]}}},
    {"type":"function","function":{
        "name":"mock_get_monitor_status",
        "description":"查看后台资源监控状态。",
        "parameters":{"type":"object","properties":{
            "monitor_id":{"type":"string","description":"监控ID"}},
            "required":["monitor_id"]}}},
    {"type":"function","function":{
        "name":"create_pending_order",
        "description":"根据已选酒店、餐厅、门票或团购项目生成待确认订单。注意：只生成待确认订单，不真实支付。",
        "parameters":{"type":"object","properties":{
            "order_type":{"type":"string","description":"hotel/restaurant/ticket/groupbuy/route_plan/trip_bundle/ride_hailing/flight_ticket"},
            "item":{"type":"object","description":"用户选择的商品、酒店、餐厅或活动"},
            "user_context":{"type":"object","description":"用户预算、人数、日期、人格等上下文"}},
            "required":["order_type","item"]}}},
    {"type":"function","function":{
        "name":"confirm_mock_order",
        "description":"用户明确确认后，执行模拟下单。黑客松演示用，不真实支付。",
        "parameters":{"type":"object","properties":{
            "order_id":{"type":"string","description":"待确认订单ID"}},
            "required":["order_id"]}}},
    {"type":"function","function":{
        "name":"patch_plan_item",
        "description":(
            "用户对已生成方案中的某个item（酒店/团购/餐厅/活动）给出反馈时，实时替换该item，不重新规划整个行程。"
            "触发场景：用户说【评分太低/换一个/太贵了/差评/不喜欢这家/换一家/这个团购不行/这个酒店评分差】"
            "且当前对话中已存在 order_id 时，必须调用此工具而非重新规划。"
            "调用前从对话历史中提取 order_id；item_type 根据用户提到的内容判断：酒店→hotel，团购→groupbuy，餐厅→restaurant，景点→activity。"
        ),
        "parameters":{"type":"object","properties":{
            "item_type":{"type":"string","enum":["hotel","groupbuy","restaurant","activity"],"description":"要替换的item类型"},
            "feedback":{"type":"string","description":"用户反馈原文，如'评分太低''太贵了''换一个'"},
            "order_id":{"type":"string","description":"当前待确认订单ID，从对话历史中提取"},
            "min_rating":{"type":"number","description":"用户要求的最低评分，如未提及则为0"},
            "max_price":{"type":"integer","description":"用户要求的最高价格，如未提及则为0"},
            "city":{"type":"string","description":"城市"},
            "user_context":{"type":"object","description":"预算、人格等上下文"}},
            "required":["item_type","feedback"]}}},
    {"type":"function","function":{
        "name":"simulate_price_scenario",
        "description":(
            "模拟不同时段/环境/事件场景下的打车价格曲线，生成24小时价格时间轴与最优叫车时段推荐。"
            "用户问【什么时候叫车最便宜/价格趋势/演唱会散场叫车/雨天打车/节假日/高峰期/几点打车便宜/加价/价格预测】时必须调用。"
            "event_type可选：auto/rush_hour_morning/rush_hour_evening/concert_end/rain/holiday_peak/new_year_eve/late_night/airport_peak/sports_event/typhoon/normal。"
        ),
        "parameters":{"type":"object","properties":{
            "service_type":{"type":"string","description":"ride_hailing/delivery/errand，默认ride_hailing"},
            "city":{"type":"string","description":"所在城市"},
            "origin":{"type":"string","description":"上车点"},
            "destination":{"type":"string","description":"目的地"},
            "event_type":{"type":"string","description":"场景类型，auto=自动判断当前时段","enum":["auto","rush_hour_morning","rush_hour_evening","concert_end","rain","holiday_peak","new_year_eve","late_night","airport_peak","sports_event","typhoon","normal"]},
            "target_hour":{"type":"integer","description":"模拟目标小时(0-23)，-1表示当前时间"},
            "user_context":{"type":"object","description":"预算、人格、行程上下文"}},
            "required":[]}}}
] + _MEITUAN_TOOLS  # ✅ 自动追加美团工具

SYSTEM_PROMPT = """你是「马到橙功」本地生活出游 Agent 的核心规划大脑。

当前系统已经接入：
1. DeepSeek API：用于意图理解、规划生成和自然语言总结。
2. 百度地图 API：用于地理编码、路线规划、距离和通勤时间估算。
3. 部分 RAG / Mock 数据：用于餐饮、酒店、排队、下单等本地生活资源演示。

当前系统暂未稳定接入完整真实美团 POI / 酒店库存 / 餐厅排队 / 真实下单接口。

因此你必须采用「真实地图 + 可信 Mock 本地生活」的规划模式。

你的目标不是聊天，而是帮用户把一次短途出游任务尽可能完整地做完：
理解需求、补全默认假设、调用地图能力、生成可执行路线、安排吃喝玩乐、控制预算、处理异常、生成待确认动作。

一、主动规划原则

1. 用户说"帮我规划""安排一下""从A去B"时，不要连续追问。
2. 如果信息缺失，必须先做合理默认假设并直接生成一版方案。
3. 默认假设必须写明，例如：
   - 默认 1 日游
   - 默认从市中心或用户给定起点出发
   - 默认交通方式为高铁 / 地铁 / 打车 / 步行组合
   - 默认预算为中等
   - 默认风格为松弛感
   - 只有用户明确说"骑行/骑车/共享单车"时，才把骑行作为路线方案
4. 只有涉及下单、支付、预约、叫车等执行动作前，才需要用户确认。
5. 初版方案必须先给出来，用户后续可以一句话调整。

二、新任务切换规则

当用户明确提出新的出游目标时，例如：
"我想去沈阳玩"、"帮我规划厦门"、"周末去杭州"、"从漳州去厦门"，
你应该静默开启新任务，并直接生成规划。

不要对用户说：
"已重置当前任务"、"请告诉我你的新需求"、"当前任务已清空"。

只有当用户单独说"重置"、"清空"、"重新开始"、"换个话题"时，
才可以回复任务已重置。

如果用户说"重新开始，我想去沈阳玩"，应静默重置旧任务，然后直接给沈阳规划。

三、真实地图使用规则

你必须优先利用百度地图能力处理：
1. 起点和终点地理解析。
2. 城市之间或城市内的距离判断。
3. 路线交通方式建议。
4. 点位之间交通时间估算。
5. 是否跨城。
6. 是否适合步行 / 打车 / 公共交通；骑行只在用户明确提出时启用。

当百度地图返回真实路线、距离或时间时：
- 必须优先使用真实路线结果。
- 不允许凭空编造距离和耗时。
- 如果地图结果不可用，可以进入 Mock 路线估算模式，并明确标注"地图接口异常，已启用估算方案"。

四、本地生活资源规则

由于当前没有稳定真实美团 POI，你不能伪造具体商户、酒店或餐厅。

允许输出三类资源：

A. 真实地图地点
如果地图 API 或用户输入返回了真实地点，可以使用。

B. 区域级建议
例如：
- 厦门中山路商圈
- 厦门沙坡尾片区
- 杭州湖滨商圈
- 上海外滩滨江区域

C. Mock 示例资源
必须明确标注："Mock 示例，用于演示端到端任务闭环"。

禁止：
1. 不要把虚构酒店/餐厅伪装成真实商户。
2. 不要给虚构商户写真实评分。
3. 不要写"美团评分 4.8"，除非工具真实返回。
4. 不要说"已真实下单"。
5. 只能说"已生成待确认动作"或"Mock 下单成功"。

四、路线完整性原则

即使没有真实 POI，也必须生成可执行路线。

每条路线至少包含 3 个节点，节点可以是：
- 交通节点
- 景点区域
- 餐饮区域
- 咖啡/休息区域
- 夜景区域
- 商圈
- 酒店区域

至少覆盖 2 类场景：
- 交通
- 景点
- 餐饮
- 休息
- 夜景
- 购物
- 周边游

每个节点必须包含：
- 时间
- 地点名称
- 类型
- 建议停留时间
- 到下一站交通方式
- 预计交通时间
- 预算估算
- 推荐理由
- 风险提示
- 数据来源：百度地图 / 区域建议 / Mock 示例

五、自然规则校验原则

你必须检查：
1. 午餐安排在 11:30-13:30。
2. 晚餐安排在 17:30-20:00。
3. 夜景安排在傍晚或晚上。
4. 咖啡/休息点安排在路线中段。
5. 跨城路线必须考虑高铁、自驾、大巴或打车成本。
6. 家庭、老人、松弛感路线不能步行过多。
7. 特种兵路线可以密集，但不能完全不留交通时间。
8. 预算必须与用户输入一致。
9. 起点和目的地不能城市错配。
10. 无法确认营业时间时，必须写"需二次确认"。

六、冲突处理原则

如果发现冲突，不要失败，要自动修正。

例如：
1. 预算太低：减少付费项目 / 降低餐饮预算 / 优先公共交通
2. 交通时间太长：减少节点 / 改成同一区域内游玩
3. 用户不想排队：避开饭点 / 准备备用餐饮区域 / 创建 Mock 排队监控
4. 天气异常：切换室内方案
5. 地图接口异常：启用估算路线 / 标注风险
6. 本地生活接口异常：启用 Mock 资源 / 保证任务继续完成

七、人格模式规则

根据用户人格调整路线：

家庭模式：安全、少走路、亲子友好、休息多、餐饮接受度高。
老年人：少换乘、少步行、白天活动、早结束、节奏慢。
社恐/i人：避开人群、少排队、安静、小众、错峰。
松弛感：少景点、慢节奏、留白时间、舒适优先。
特种兵：效率优先、多节点、交通最快、时间压缩。
穷游大学生：免费区域、低价餐饮、公共交通优先、预算优先。
出片党：日落、夜景、滨水、街区、咖啡、拍照点。
美食脑袋：餐饮权重最高、本地特色、夜宵、预算向吃倾斜。

八、Mock 执行规则

你可以生成 Mock 执行动作，但必须标注为 Mock。

允许生成：
- Mock 酒店待确认订单
- Mock 餐厅取号
- Mock 打车
- Mock 排队监控
- Mock 行程确认卡

只有用户明确说"确认""就这个""帮我订""开始执行"才可以输出"Mock 执行成功"。

九、动态调整规则

用户要求调整时，不要整条路线重做。

例如用户说：换一家餐厅 / 少走路 / 预算降低 / 不想排队 / 改成适合拍照 / 改成带爸妈版本

你必须局部调整，并说明：
1. 替换了什么
2. 为什么替换
3. 对预算的影响
4. 对时间的影响
5. 对路线强度的影响

十、输出格式（地图优先，首屏不超过 300 字）

用户提出出游/路线/citywalk/吃喝玩乐需求时，必须先输出"地图式路线摘要"，再给详情。
首屏只展示路线节点、关键指标、风险标签、操作按钮，详细攻略默认折叠。

【一句话方案摘要】
一句话告知：适合什么人 · 节奏如何 · 核心亮点。不超过 30 字。

【推荐路线地图】
按 1 → 2 → ... 方式列出节点，每个节点不超过 18 字。
格式：
1. 节点名称（类型）停留 xx 分钟
   ↓ 交通方式 约 xx 分钟
2. ...
至少 3 个节点，覆盖至少 2 类场景（景点/餐饮/咖啡/夜景/商圈）。

【关键指标】
总耗时 / 总预算 / 路线强度 / 步行强度 / 排队风险 / 数据可信度

【时间线详情】（默认折叠，用户展开后显示）
09:30 → ... 按时间输出每个节点

【风险与兜底】（默认折叠）
- 可能排队的地方
- 需要二次确认的地方
- 下雨/超预算备选

【可操作按钮】
输出 4-6 个按钮供前端渲染：换成更省钱 / 换成更松弛 / 换成特种兵 / 避开排队 / 生成待确认订单 / 开启排队监控

JSON 部分必须紧跟自然语言之后输出，供前端渲染路线地图卡：

{
  "answer_type": "map_first_trip_plan",
  "summary": "",
  "route_map": [
    {
      "step": 1,
      "name": "",
      "type": "",
      "short_desc": "",
      "stay_minutes": 0,
      "next_transport": "",
      "next_duration_minutes": 0,
      "data_source": "",
      "is_real_poi": false,
      "need_verify": false
    }
  ],
  "metrics": {
    "total_duration_minutes": 0,
    "total_budget": 0,
    "route_intensity": "",
    "walking_intensity": "",
    "queue_risk": "",
    "data_confidence": ""
  },
  "timeline": [
    {
      "time": "",
      "title": "",
      "detail": "",
      "cost": 0,
      "risk": ""
    }
  ],
  "fallbacks": [
    {
      "trigger": "",
      "backup_plan": ""
    }
  ],
  "actions": [
    {
      "label": "",
      "action_type": "",
      "requires_confirm": false
    }
  ]
}

十一、多轮任务状态规则（必须严格执行）

你必须把当前对话视为一个持续任务，而不是每轮重新开始。

1. 如果上一轮给出了方案1/2/3，用户输入以下任意内容：
   - 数字：1、2、3
   - 文字：方案一、第二个、就这个、确认
   必须理解为用户在选择上一轮方案，而不是开启新话题。

2. 任务边界规则：
   - 当前任务未完成时，禁止主动跳到其他城市或其他话题。
   - 如果历史里出现过多个城市，以最近一次明确任务为准。
   - 只有用户明确说"重新开始""换个话题""取消"才允许切换任务。

3. 用户选择方案后，你必须：
   - 复述用户选择的方案
   - 说明执行了什么动作
   - 更新任务状态
   - 给出下一步可确认动作

4. 方案输出格式（给出方案时必须用此格式，方便后端解析）：
   方案1：[简短标题，不超过20字]
   方案2：[简短标题，不超过20字]
   方案3：[简短标题，不超过20字]

5. 如果用户输入很短（如"3""确认""就这个"），优先结合上一轮候选方案理解，不要孤立解释这句话。

6. 确认下单/执行规则：
   - 用户说"确认""就这个""帮我订"时，输出"Mock 执行成功"并描述执行结果。
   - 不要再追问，直接给结果。

语气专业友好，数据详细具体，结尾加🍊鼓励语。"""


def _meituan_trip_final_text(plan: dict) -> str:
    if not plan.get("success", True):
        return _clean_markdown(plan.get("error", "行程规划失败，请稍后重试。"))
    if plan.get("route_card"):
        return json.dumps(plan["route_card"], ensure_ascii=False)
    req = plan.get("requirements", {})
    budget = plan.get("budget", {})
    weather = plan.get("weather", {})
    hotels = plan.get("hotels", [])
    days = plan.get("days", [])
    weather_line = "天气暂不可用，按常规出行准备即可。"
    if weather.get("available"):
        weather_line = f"{weather.get('city')} {weather.get('text')}，{weather.get('temp')}℃，{weather.get('wind')}。"
    hotel_line = "、".join([f"{h.get('name')}({h.get('rating')}分/约¥{h.get('cost')})" for h in hotels[:3]])
    day_lines = "\n".join([
        f"D{d.get('day')} {d.get('theme')}：{' → '.join(d.get('route', []))}；美食：{d.get('food')}；预算约¥{d.get('budget')}"
        for d in days
    ])
    pending = plan.get("pending_order") or {}
    pending_line = ""
    if pending.get("order_id"):
        item = pending.get("item") or {}
        pending_line = (
            f"\n\n【待确认动作】已生成待确认订单 {pending.get('order_id')}："
            f"{item.get('name','出游资源包')}，预估¥{item.get('price_estimate','-')}。"
            "用户确认后执行模拟下单，不触碰真实支付。"
        )
    proactive = plan.get("proactive_defaults") or {}
    proactive_text = ""
    if proactive.get("enabled"):
        assumptions = "、".join(proactive.get("assumptions") or [])
        workflow = "\n".join([f"✅ {step}" for step in proactive.get("workflow") or []])
        proactive_text = (
            f"{proactive.get('intro', '🍊 我先生成可执行草案，不打断你。')}\n"
            f"已默认：{assumptions}。\n"
            f"{workflow}\n\n"
        )
    # 要求9：出发地是默认值时加说明
    _origin_note = ""
    if req.get("origin_is_default"):
        _origin_note = f"（出发地按当前城市/默认出发规划，如需修改出发地可随时告知我）\n\n"
    if plan.get("commerce_mode") == "none":
        return _clean_markdown(
            proactive_text +
            _origin_note +
            f"【行程速览】{req.get('destination')} {req.get('days')}天独立行程规划，总预算¥{budget.get('total')}，核心是路线、景点、餐饮建议和预算控制。\n\n"
            f"【天气速览卡片】{weather_line} 天气只做辅助，行程主线已固定。\n\n"
            "【景点与餐饮建议】已按你的偏好避开交易入口，仅保留可自行选择的景点与餐饮参考。\n\n"
            f"【{req.get('days')}天行程路线卡片】\n{day_lines}\n\n"
            f"【综合结论】预算分配：住宿预留¥{budget.get('hotel')}、交通¥{budget.get('transport')}、餐饮¥{budget.get('food')}、门票¥{budget.get('tickets')}、市内交通¥{budget.get('local')}、机动¥{budget.get('buffer')}。"
            "已按你的要求避开美团下单，仅做独立行程规划。🍊"
        )
    if plan.get("fallback_used"):
        return _clean_markdown(
            proactive_text +
            f"【行程速览】{req.get('destination')} {req.get('days')}天，总预算¥{budget.get('total')}，核心是路线、预算和本地资源安排。\n\n"
            f"【天气速览卡片】{weather_line} 天气只做辅助，行程主线已固定。\n\n"
            f"【资源推荐】美团 Skill 暂不可用，未展示店名：{hotel_line}。\n\n"
            f"【{req.get('days')}天行程路线卡片】\n{day_lines}\n\n"
            f"【综合结论】预算分配：住宿¥{budget.get('hotel')}、交通¥{budget.get('transport')}、餐饮¥{budget.get('food')}、门票¥{budget.get('tickets')}、市内交通¥{budget.get('local')}、机动¥{budget.get('buffer')}。"
            "这版已把行程、预算、资源建议和交通方式串完整。🍊"
        )
    return _clean_markdown(
        proactive_text +
        f"【行程速览】{req.get('destination')} {req.get('days')}天，总预算¥{budget.get('total')}，核心是园林/老城/夜游 + 美团酒店控预算。\n\n"
        f"【天气速览卡片】{weather_line} 天气只做辅助，行程主线已固定。\n\n"
        f"【美团酒店推荐】{hotel_line}。均按美团高评分、预算友好、交通方便筛选。\n\n"
        f"【{req.get('days')}天行程路线卡片】\n{day_lines}\n\n"
        f"【综合结论】预算分配：酒店¥{budget.get('hotel')}、交通¥{budget.get('transport')}、餐饮¥{budget.get('food')}、门票¥{budget.get('tickets')}、市内交通¥{budget.get('local')}、机动¥{budget.get('buffer')}。"
        f"这版已经把行程、预算、美团酒店/美食/景点和交通方式闭环。{pending_line}🍊"
    )

def _deepseek_trip_final_text(planning_context: dict) -> str:
    if not DEEPSEEK_API_KEY or not isinstance(planning_context, dict):
        return ""
    try:
        messages = [
            {
                "role": "system",
                "content": (
                    "你是马到橙功出游 Agent。必须基于工具返回的真实 JSON 数据生成可信、可执行旅行规划。\n"
                    "【严格禁止】：\n"
                    "1. 禁止输出[XX代表性景区区域][XX核心商圈餐饮区域]等模板化地点标题。\n"
                    "2. 禁止把用户的原始话术（如[帮我做个][规划][攻略]）拼入地点名称。\n"
                    "3. 禁止将 data_level=C_MOCK_REGION 的区域建议包装成真实商户或生成订单。\n"
                    "4. 禁止混用跨城市资源。\n"
                    "【必须做到】：\n"
                    "1. 如果 meituan_hotels/meituan_restaurants/meituan_spots 有 data_level=A_REAL_MEITUAN 的真实商户，必须优先展示真实名称。\n"
                    "2. 如果只有 area_suggestions（data_level=C_MOCK_REGION），必须明确标注[区域建议，不代表具体商户，不生成订单]。\n"
                    "3. 输出必须是一个 JSON 对象，answer_type 必须是 map_first_trip_plan。\n"
                    "4. route_map 至少3个节点，覆盖至少2类场景；节点标题要短，不超过18字。\n"
                    "5. 输出中文，像路线地图卡，不要输出长段攻略文字。"
                ),
            },
            {
                "role": "user",
                "content": (
                    "用户需求与工具结果 JSON 如下：\n"
                    f"{json.dumps(planning_context, ensure_ascii=False, indent=2)[:12000]}\n\n"
                    "请优先复用 route_card，并只输出严格 JSON："
                    "{answer_type, summary, route_map, metrics, timeline, fallbacks, actions}。"
                    "不要输出 Markdown，不要输出解释。"
                ),
            },
        ]
        resp = requests.post(DEEPSEEK_URL, headers={
            "Authorization": f"Bearer {DEEPSEEK_API_KEY}",
            "Content-Type": "application/json",
        }, json={
            "model": DEEPSEEK_MODEL,
            "messages": messages,
            "max_tokens": 1200,
            "temperature": 0.25,
        }, timeout=DEEPSEEK_TIMEOUT)
        resp.raise_for_status()
        data = resp.json()
        text = _clean_markdown(data.get("choices", [{}])[0].get("message", {}).get("content", ""))
        if '"answer_type"' not in text or "map_first_trip_plan" not in text:
            return ""
        return text
    except Exception as e:
        print(f"[deepseek_trip_final]{_safe_error_text(e)}")
        return ""


def _panorama_final_text(plan: dict) -> str:
    origin = plan.get("origin", {}).get("name", "")
    dest = plan.get("destination", {}).get("name", "")
    decision = plan.get("decision", {})
    long_legs = plan.get("long_distance", [])
    local_legs = plan.get("local_transfer", [])
    weather = plan.get("weather", {})
    flight = plan.get("flight_query", {})
    main_leg = long_legs[0] if long_legs else (local_legs[0] if local_legs else {})
    local = local_legs[0] if local_legs else {}
    weather_line = ""
    if weather.get("available"):
        weather_line = f"\n天气辅助：{weather.get('city')} {weather.get('text')}，{weather.get('temp')}℃，{weather.get('wind')}。"
    flight_line = ""
    if flight.get("enabled"):
        flight_line = f"\n航班查询：{flight.get('origin_airport')} → {flight.get('destination_airport')}；{flight.get('reason')}"
    return _clean_markdown(
        f"{origin} → {dest} 全景出行方案\n"
        f"判定：{decision.get('label')}，直线约 {plan.get('distance_km')} km，{decision.get('priority')}。\n\n"
        f"主交通：{main_leg.get('title','')}，{main_leg.get('route','')}，{main_leg.get('duration','')}。\n"
        f"市内接驳：{local.get('mode','')}，{local.get('route','')}，{local.get('duration','')}。"
        f"{flight_line}{weather_line}\n\n"
        "步行作为最后一公里备选；骑行只在用户明确提出时启用，不会替代跨城或跨国主交通。🍊"
    )


def _weekend_final_text(plan: dict) -> str:
    stops = plan.get("stops", [])
    acts = plan.get("activities", [])
    stop_line = " → ".join([s.get("name","") for s in stops])
    act_line = "、".join([a.get("name","") for a in acts[:3]])
    route = plan.get("route", {})
    provider = {"gaode":"高德地图","baidu":"百度地图","google":"Google Maps"}.get(plan.get("map_provider"), "地图")
    return _clean_markdown(
        f"{plan.get('title','周末出行方案')}\n"
        f"我已按 {plan.get('persona_label') or '当前偏好'} 压缩成可执行半日线。\n\n"
        f"路线：{stop_line}\n"
        f"预计：约 {route.get('distance_km')} km，{route.get('duration_min')} 分钟\n"
        f"打开：优先用 {provider}，同时保留百度/高德/Google 三种链接\n\n"
        f"活动：{act_line}\n"
        "异常处理：排队超过 20 分钟自动换同街区备选；导航异常时保留同方向可执行路线。\n"
        "这版已经把路线、链接、活动和后续安排串成完整任务。🍊"
    )


def _rule_meituan_trip_agent_response(user_message: str, city_hint: str,
                                      persona: str, map_provider: str) -> Response:
    def generate():
        req = _extract_trip_requirements(user_message, city_hint)
        tool_name = "independent_trip_planner" if req.get("planner_mode") == "independent_trip" else "plan_meituan_trip"
        args = {
            "city": city_hint,
            "user_prompt": user_message,
            "persona": persona,
            "map_provider": map_provider or "gaode",
        }
        yield f"data: {json.dumps({'type':'step_start','id':1,'tool':tool_name,'input':args}, ensure_ascii=False)}\n\n"
        if req.get("planner_mode") == "meituan_commerce":
            mt_input = {"intent": "hotel_search" if req.get("wants_hotel") else "restaurant_search",
                        "city": req.get("destination"), "keyword": "酒店/本地菜/景点", "limit": 6}
            yield f"data: {json.dumps({'type':'step_start','id':2,'tool':'call_meituan_skill','input':mt_input}, ensure_ascii=False)}\n\n"
        plan = tool_plan_meituan_trip(**args)
        if req.get("planner_mode") == "meituan_commerce":
            mt_results = []
            if plan.get("success"):
                mt_results = [x for x in (plan.get("hotels") or []) + (plan.get("foods") or []) + (plan.get("sights") or []) if _is_real_meituan_item(x)]
            mt_payload = {
                "success": bool(plan.get("success") and mt_results),
                "city": req.get("destination"),
                "keyword": "酒店/本地菜/景点",
                "count": len(mt_results),
                "results": mt_results[:6],
                "source": "meituan_skill",
                "is_real_meituan": bool(mt_results),
                "message": "" if mt_results else plan.get("fallback_message", "美团搜索🔍 暂无真实商户结果，已切换区域建议。"),
            }
            mt_summary = _tool_summary("call_meituan_skill", mt_input, mt_payload)
            yield f"data: {json.dumps({'type':'step_done','id':2,'tool':'call_meituan_skill','result':mt_payload,'summary':mt_summary}, ensure_ascii=False)}\n\n"
        if plan.get("success") and plan.get("pending_order"):
            order_payload = {"success": True, "order": plan["pending_order"]}
            order_input = {
                "order_type": plan["pending_order"].get("order_type", "trip_bundle"),
                "item": plan["pending_order"].get("item", {}),
            }
            yield f"data: {json.dumps({'type':'step_start','id':3,'tool':'create_pending_order','input':order_input}, ensure_ascii=False)}\n\n"
            yield f"data: {json.dumps({'type':'step_done','id':3,'tool':'create_pending_order','result':order_payload,'summary':_tool_summary('create_pending_order', {}, order_payload)}, ensure_ascii=False)}\n\n"
        sm = _tool_summary(tool_name, args, plan)
        yield f"data: {json.dumps({'type':'step_done','id':1,'tool':tool_name,'result':plan,'summary':sm}, ensure_ascii=False)}\n\n"
        final_text = _deepseek_trip_final_text(plan.get("planning_context", {})) if plan.get("success") else ""
        yield f"data: {json.dumps({'type':'final','text':final_text or _meituan_trip_final_text(plan)}, ensure_ascii=False)}\n\n"
    return Response(stream_with_context(generate()), mimetype="text/event-stream",
                    headers={"Cache-Control":"no-cache","X-Accel-Buffering":"no"})

def _rule_meituan_resource_agent_response(user_message: str, city_hint: str) -> Response:
    def generate():
        args = _direct_meituan_skill_input(user_message, city_hint)
        yield f"data: {json.dumps({'type':'step_start','id':1,'tool':'call_meituan_skill','input':args}, ensure_ascii=False)}\n\n"
        result = tool_call_meituan_skill(
            intent=args["intent"],
            city=args["city"],
            keyword=args["keyword"],
            location=args["location"],
            user_lat=args["user_lat"],
            user_lng=args["user_lng"],
            filters=args["filters"],
            limit=args["limit"],
        )
        summary = _tool_summary("call_meituan_skill", args, result)
        yield f"data: {json.dumps({'type':'step_done','id':1,'tool':'call_meituan_skill','result':result,'summary':summary}, ensure_ascii=False)}\n\n"
        pending_order = {}
        if result.get("success") and result.get("results") and _looks_order_draft_request(user_message):
            item = _build_resource_order_item(args, result)
            order_type = "hotel" if args.get("intent") == "hotel_search" else "restaurant" if args.get("intent") in ("restaurant_search", "nearby_search") else "ticket" if args.get("intent") == "ticket_search" else "groupbuy"
            order_result = tool_create_pending_order(
                order_type=order_type,
                item=item,
                user_context={
                    "city": args.get("city", city_hint),
                    "keyword": args.get("keyword", ""),
                    "source": result.get("source", "meituan_skill"),
                }
            )
            pending_order = order_result.get("order", {})
            yield f"data: {json.dumps({'type':'step_start','id':2,'tool':'create_pending_order','input':{'order_type':order_type,'item':item}}, ensure_ascii=False)}\n\n"
            yield f"data: {json.dumps({'type':'step_done','id':2,'tool':'create_pending_order','result':order_result,'summary':_tool_summary('create_pending_order', {}, order_result)}, ensure_ascii=False)}\n\n"
        if result.get("success") and result.get("results"):
            names = "、".join([x.get("name", "") for x in result.get("results", [])[:3] if x.get("name")])
            if args.get("user_lat") and args.get("user_lng"):
                text = f"已按你的当前位置匹配美团真实资源：{names}。"
            else:
                text = f"已按{args.get('city') or city_hint}匹配美团真实资源：{names}。"
            if pending_order.get("order_id"):
                text += f" 已生成待确认订单 {pending_order['order_id']}，请在卡片中确认后执行模拟下单。"
        else:
            text = result.get("message") or result.get("error") or MEITUAN_SKILL_UNAVAILABLE
        yield f"data: {json.dumps({'type':'final','text':text}, ensure_ascii=False)}\n\n"
    return Response(stream_with_context(generate()), mimetype="text/event-stream",
                    headers={"Cache-Control":"no-cache","X-Accel-Buffering":"no"})

def _rule_confirm_order_response(user_message: str) -> Response:
    def generate():
        order_id = _extract_order_id(user_message)
        args = {"order_id": order_id}
        yield f"data: {json.dumps({'type':'step_start','id':1,'tool':'confirm_mock_order','input':args}, ensure_ascii=False)}\n\n"
        result = tool_confirm_mock_order(order_id)
        summary = _tool_summary("confirm_mock_order", args, result)
        yield f"data: {json.dumps({'type':'step_done','id':1,'tool':'confirm_mock_order','result':result,'summary':summary}, ensure_ascii=False)}\n\n"
        text = result.get("message") if result.get("success") else result.get("error", "订单确认失败")
        yield f"data: {json.dumps({'type':'final','text':text}, ensure_ascii=False)}\n\n"
    return Response(stream_with_context(generate()), mimetype="text/event-stream",
                    headers={"Cache-Control":"no-cache","X-Accel-Buffering":"no"})


def _mock_weekend_agent_response(user_message: str, city_hint: str,
                                 persona: str, route_profile: str,
                                 map_provider: str) -> Response:
    def generate():
        args = {
            "city": _infer_weekend_city(user_message, city_hint),
            "user_prompt": user_message,
            "persona": persona,
            "route_profile": route_profile,
            "map_provider": map_provider or "gaode",
            "duration_hours": 4,
        }
        yield f"data: {json.dumps({'type':'step_start','id':1,'tool':'plan_weekend_trip','input':args}, ensure_ascii=False)}\n\n"
        plan = tool_plan_weekend_trip(**args)
        sm = _tool_summary("plan_weekend_trip", args, plan)
        yield f"data: {json.dumps({'type':'step_done','id':1,'tool':'plan_weekend_trip','result':plan,'summary':sm}, ensure_ascii=False)}\n\n"
        yield f"data: {json.dumps({'type':'final','text':_weekend_final_text(plan)}, ensure_ascii=False)}\n\n"
    return Response(stream_with_context(generate()), mimetype="text/event-stream",
                    headers={"Cache-Control":"no-cache","X-Accel-Buffering":"no"})


def _mock_panorama_agent_response(user_message: str, city_hint: str,
                                  persona: str, map_provider: str) -> Response:
    def generate():
        args = {
            "city": city_hint,
            "user_prompt": user_message,
            "persona": persona,
            "map_provider": map_provider or "gaode",
        }
        yield f"data: {json.dumps({'type':'step_start','id':1,'tool':'plan_panorama_trip','input':args}, ensure_ascii=False)}\n\n"
        plan = tool_plan_panorama_trip(**args)
        sm = _tool_summary("plan_panorama_trip", args, plan)
        yield f"data: {json.dumps({'type':'step_done','id':1,'tool':'plan_panorama_trip','result':plan,'summary':sm}, ensure_ascii=False)}\n\n"
        yield f"data: {json.dumps({'type':'final','text':_panorama_final_text(plan)}, ensure_ascii=False)}\n\n"
    return Response(stream_with_context(generate()), mimetype="text/event-stream",
                    headers={"Cache-Control":"no-cache","X-Accel-Buffering":"no"})


def run_deepseek_agent(user_message: str, city_hint: str = "上海",
                       history: list = None, persona: str = "",
                       route_profile: str = "", route_strategy: str = "",
                       map_provider: str = "", extra_system: str = "") -> Response:
    _update_soul_memory_from_message(user_message)
    if _extract_order_id(user_message) and re.search(r"确认|下单|预订|就这个", user_message):
        return _rule_confirm_order_response(user_message)
    if _looks_mock_resource_task(user_message):
        return _rule_mock_resource_agent_response(user_message, city_hint, persona, map_provider)
    if _looks_direct_meituan_resource(user_message):
        return _rule_meituan_resource_agent_response(user_message, city_hint)
    if _looks_meituan_trip(user_message):
        return _rule_meituan_trip_agent_response(user_message, city_hint, persona, map_provider)
    if not DEEPSEEK_API_KEY:
        if _looks_panorama_trip(user_message):
            return _mock_panorama_agent_response(user_message, city_hint, persona, map_provider)
        if _looks_weekend_trip(user_message):
            return _mock_weekend_agent_response(user_message, city_hint, persona,
                                                route_profile, map_provider)
        def _nk():
            yield f"data: {json.dumps({'type':'error','text':'请设置DEEPSEEK_API_KEY'}, ensure_ascii=False)}\n\n"
        return Response(stream_with_context(_nk()), mimetype="text/event-stream")

    hdrs = {"Authorization":f"Bearer {DEEPSEEK_API_KEY}","Content-Type":"application/json"}

    # ✅ 多轮记忆：最近6轮 + 任务状态（由调用方通过 _build_clean_history 传入）
    system_prompt = (SYSTEM_PROMPT + "\n\n"
                     + _route_context(persona, route_profile, route_strategy)
                     + "\n\n" + _soul_context(user_message)
                     + (extra_system or ""))
    msgs = [{"role":"system","content":system_prompt}]
    if history:
        for h in history:  # 调用方已限制6轮
            role = h.get("role","")
            content = h.get("content","")
            if role in ("user","assistant") and content:
                msgs.append({"role":role,"content":content})
    msgs.append({"role":"user","content":user_message})

    def generate():
        sidx = 0
        final_text = ""
        used_panorama_tool = False
        used_weekend_tool = False
        for _ in range(8):
            try:
                resp = requests.post(DEEPSEEK_URL, headers=hdrs, json={
                    "model":DEEPSEEK_MODEL,"messages":msgs,
                    "tools":AGENT_TOOLS,"tool_choice":"auto",
                    "max_tokens":2000,"temperature":0.3}, timeout=DEEPSEEK_TIMEOUT)
                resp.raise_for_status()
                result = resp.json()
            except Exception as e:
                if _looks_panorama_trip(user_message):
                    args = {
                        "city": city_hint,
                        "user_prompt": user_message,
                        "persona": persona,
                        "map_provider": map_provider or "gaode",
                    }
                    sidx += 1
                    yield f"data: {json.dumps({'type':'step_start','id':sidx,'tool':'plan_panorama_trip','input':args}, ensure_ascii=False)}\n\n"
                    plan = tool_plan_panorama_trip(**args)
                    sm = _tool_summary("plan_panorama_trip", args, plan)
                    yield f"data: {json.dumps({'type':'step_done','id':sidx,'tool':'plan_panorama_trip','result':plan,'summary':sm}, ensure_ascii=False)}\n\n"
                    yield f"data: {json.dumps({'type':'final','text':_panorama_final_text(plan)}, ensure_ascii=False)}\n\n"
                    return
                if _looks_weekend_trip(user_message):
                    args = {
                        "city": _infer_weekend_city(user_message, city_hint),
                        "user_prompt": user_message,
                        "persona": persona,
                        "route_profile": route_profile,
                        "map_provider": map_provider or "gaode",
                        "duration_hours": 4,
                    }
                    sidx += 1
                    yield f"data: {json.dumps({'type':'step_start','id':sidx,'tool':'plan_weekend_trip','input':args}, ensure_ascii=False)}\n\n"
                    plan = tool_plan_weekend_trip(**args)
                    sm = _tool_summary("plan_weekend_trip", args, plan)
                    yield f"data: {json.dumps({'type':'step_done','id':sidx,'tool':'plan_weekend_trip','result':plan,'summary':sm}, ensure_ascii=False)}\n\n"
                    yield f"data: {json.dumps({'type':'final','text':_weekend_final_text(plan)}, ensure_ascii=False)}\n\n"
                    return
                recovery_text = (
                    "🍊 正在为你生成出行方案，稍等片刻…"
                )
                yield f"data: {json.dumps({'type':'step_info','text':recovery_text}, ensure_ascii=False)}\n\n"
                return

            ch = result["choices"][0]
            msg = ch["message"]
            finish = ch.get("finish_reason","")

            if finish == "stop":
                if _looks_panorama_trip(user_message) and not used_panorama_tool:
                    args = {
                        "city": city_hint,
                        "user_prompt": user_message,
                        "persona": persona,
                        "map_provider": map_provider or "gaode",
                    }
                    sidx += 1
                    yield f"data: {json.dumps({'type':'step_start','id':sidx,'tool':'plan_panorama_trip','input':args}, ensure_ascii=False)}\n\n"
                    plan = tool_plan_panorama_trip(**args)
                    sm = _tool_summary("plan_panorama_trip", args, plan)
                    yield f"data: {json.dumps({'type':'step_done','id':sidx,'tool':'plan_panorama_trip','result':plan,'summary':sm}, ensure_ascii=False)}\n\n"
                    yield f"data: {json.dumps({'type':'final','text':_panorama_final_text(plan)}, ensure_ascii=False)}\n\n"
                    return
                if _looks_weekend_trip(user_message) and not used_weekend_tool:
                    args = {
                        "city": _infer_weekend_city(user_message, city_hint),
                        "user_prompt": user_message,
                        "persona": persona,
                        "route_profile": route_profile,
                        "map_provider": map_provider or "gaode",
                        "duration_hours": 4,
                    }
                    sidx += 1
                    yield f"data: {json.dumps({'type':'step_start','id':sidx,'tool':'plan_weekend_trip','input':args}, ensure_ascii=False)}\n\n"
                    plan = tool_plan_weekend_trip(**args)
                    sm = _tool_summary("plan_weekend_trip", args, plan)
                    yield f"data: {json.dumps({'type':'step_done','id':sidx,'tool':'plan_weekend_trip','result':plan,'summary':sm}, ensure_ascii=False)}\n\n"
                    yield f"data: {json.dumps({'type':'final','text':_weekend_final_text(plan)}, ensure_ascii=False)}\n\n"
                    return
                final_text = _clean_markdown(msg.get("content",""))
                yield f"data: {json.dumps({'type':'final','text':final_text}, ensure_ascii=False)}\n\n"
                return

            if finish == "tool_calls" or msg.get("tool_calls"):
                msgs.append(msg)
                tres = []
                for tc in msg.get("tool_calls",[]):
                    fn = tc["function"]["name"]
                    try: fa = json.loads(tc["function"]["arguments"])
                    except: fa = {}
                    sidx += 1
                    yield f"data: {json.dumps({'type':'step_start','id':sidx,'tool':fn,'input':fa}, ensure_ascii=False)}\n\n"

                    if fn == "get_weather":
                        tr = tool_get_weather(fa.get("city", city_hint))
                    elif fn == "plan_meituan_trip":
                        tr = tool_plan_meituan_trip(
                            city         = fa.get("city", city_hint),
                            user_prompt  = fa.get("user_prompt", user_message),
                            persona      = fa.get("persona", persona),
                            map_provider = fa.get("map_provider", map_provider),
                        )
                    elif fn == "plan_panorama_trip":
                        used_panorama_tool = True
                        tr = tool_plan_panorama_trip(
                            city         = fa.get("city", city_hint),
                            user_prompt  = fa.get("user_prompt", user_message),
                            origin       = fa.get("origin", ""),
                            destination  = fa.get("destination", ""),
                            persona      = fa.get("persona", persona),
                            map_provider = fa.get("map_provider", map_provider),
                        )
                    elif fn == "plan_weekend_trip":
                        used_weekend_tool = True
                        tr = tool_plan_weekend_trip(
                            city          = fa.get("city", city_hint),
                            user_prompt   = fa.get("user_prompt", user_message),
                            persona       = fa.get("persona", persona),
                            route_profile = fa.get("route_profile", route_profile),
                            map_provider  = fa.get("map_provider", map_provider),
                            duration_hours= float(fa.get("duration_hours", 4) or 4),
                        )
                    elif fn == "plan_route":
                        tr = tool_plan_route(fa.get("city",city_hint),fa.get("start",""),
                                             fa.get("destination",""),fa.get("riding_type",0),
                                             _optional_int(fa.get("road_prefer")),
                                             fa.get("route_profile", route_profile),
                                             fa.get("persona", persona),
                                             fa.get("route_strategy", route_strategy))
                    elif fn == "search_michelin":
                        tr = tool_search_michelin(fa.get("query",""))
                    elif fn == "call_meituan_skill":
                        tr = tool_call_meituan_skill(
                            intent      = fa.get("intent", "restaurant_search"),
                            city        = fa.get("city", city_hint),
                            keyword     = fa.get("keyword", ""),
                            location    = fa.get("location", ""),
                            user_lat    = fa.get("user_lat"),
                            user_lng    = fa.get("user_lng"),
                            filters     = fa.get("filters", {}),
                            limit       = int(fa.get("limit", 5)),
                        )
                    elif fn == "find_nearest_michelin":
                        tr = tool_find_nearest_michelin(
                            lat=float(fa.get("lat",0)),
                            lng=float(fa.get("lng",0)),
                            limit=int(fa.get("limit",5)),
                            cuisine_filter=fa.get("cuisine_filter","")
                        )
                    elif fn == "mock_request_ride":
                        tr = tool_mock_request_ride(
                            origin=fa.get("origin", ""),
                            destination=fa.get("destination", ""),
                            city=fa.get("city", city_hint),
                            trigger_reason=fa.get("trigger_reason", user_message),
                            user_context=fa.get("user_context", {}),
                        )
                    elif fn == "mock_search_flights":
                        tr = tool_mock_search_flights(
                            origin=fa.get("origin", ""),
                            destination=fa.get("destination", ""),
                            date=fa.get("date", ""),
                            budget=int(fa.get("budget", 0) or 0),
                            passengers=int(fa.get("passengers", 1) or 1),
                            cabin=fa.get("cabin", "economy"),
                            user_context=fa.get("user_context", {}),
                        )
                    elif fn == "mock_start_service_monitor":
                        tr = tool_mock_start_service_monitor(
                            resource_type=fa.get("resource_type", "queue"),
                            target_name=fa.get("target_name", ""),
                            city=fa.get("city", city_hint),
                            condition=fa.get("condition", user_message),
                            callback_action=fa.get("callback_action", ""),
                            duration_minutes=int(fa.get("duration_minutes", 30) or 30),
                            user_context=fa.get("user_context", {}),
                        )
                    elif fn == "mock_get_monitor_status":
                        tr = tool_mock_get_monitor_status(fa.get("monitor_id", ""))
                    elif fn == "create_pending_order":
                        tr = tool_create_pending_order(
                            order_type=fa.get("order_type", "unknown"),
                            item=fa.get("item", {}),
                            user_context=fa.get("user_context", {}),
                        )
                    elif fn == "confirm_mock_order":
                        tr = tool_confirm_mock_order(fa.get("order_id", ""))
                    elif fn == "patch_plan_item":
                        tr = tool_patch_plan_item(
                            item_type=fa.get("item_type","hotel"),
                            feedback=fa.get("feedback",""),
                            order_id=fa.get("order_id",""),
                            min_rating=float(fa.get("min_rating",0) or 0),
                            max_price=int(fa.get("max_price",0) or 0),
                            city=fa.get("city",city_hint),
                            user_context=fa.get("user_context",{}),
                        )
                    elif fn == "simulate_price_scenario":
                        tr = tool_simulate_price_scenario(
                            service_type=fa.get("service_type", "ride_hailing"),
                            city=fa.get("city", city_hint),
                            origin=fa.get("origin", ""),
                            destination=fa.get("destination", ""),
                            event_type=fa.get("event_type", "auto"),
                            target_hour=int(fa.get("target_hour", -1) or -1),
                            user_context=fa.get("user_context", {}),
                        )
                    else:
                        tr = {"success":False,"error":f"未知工具：{fn}"}

                    sm = _clean_markdown(_tool_summary(fn, fa, tr))
                    yield f"data: {json.dumps({'type':'step_done','id':sidx,'tool':fn,'result':tr,'summary':sm}, ensure_ascii=False)}\n\n"
                    tres.append({"role":"tool","tool_call_id":tc["id"],"content":json.dumps(tr,ensure_ascii=False)})
                msgs.extend(tres)
                continue
            break

        yield f"data: {json.dumps({'type':'final','text':'推理完成。🍊'}, ensure_ascii=False)}\n\n"

    return Response(stream_with_context(generate()), mimetype="text/event-stream",
                    headers={"Cache-Control":"no-cache","X-Accel-Buffering":"no"})


# ══ HTTP 路由 ══

@app.route("/api/weather", methods=["GET"])
def api_weather():
    r = tool_get_weather(request.args.get("city","上海").strip())
    if r.get("success"): return jsonify({"status":"success","city":r["city"],"data":r["data"]})
    return jsonify({"status":"error","message":r.get("error")}), 404


@app.route("/api/plan_route", methods=["POST"])
def api_plan_route():
    b = request.get_json(force=True)
    if not b.get("destination","").strip(): return jsonify({"error":"destination不能为空"}), 400
    r = tool_plan_route(b.get("city","上海").strip(),b.get("start_addr","").strip(),
                        b.get("destination","").strip(),
                        int(b.get("riding_type",0)),
                        _optional_int(b.get("road_prefer")),
                        b.get("route_profile",""),
                        b.get("persona",""),
                        b.get("route_strategy",""))
    if r.get("success"): return jsonify(r)
    return jsonify({"error":r.get("error")}), 502

@app.route("/api/order/create_pending", methods=["POST"])
def api_create_pending_order():
    b = request.get_json(force=True)
    r = tool_create_pending_order(
        order_type=b.get("order_type", "hotel"),
        item=b.get("item", {}),
        user_context=b.get("user_context", {}),
    )
    return jsonify(r)


@app.route("/api/order/confirm_mock", methods=["POST"])
def api_confirm_mock_order():
    b = request.get_json(force=True)
    order_id = b.get("order_id", "")
    if not order_id:
        return jsonify({"success": False, "error": "order_id不能为空"}), 400
    r = tool_confirm_mock_order(order_id)
    return jsonify(r)

@app.route("/api/mock/ride_quote", methods=["POST"])
def api_mock_ride_quote():
    b = request.get_json(force=True)
    return jsonify(tool_mock_request_ride(
        origin=b.get("origin", ""),
        destination=b.get("destination", ""),
        city=b.get("city", ""),
        trigger_reason=b.get("trigger_reason", ""),
        user_context=b.get("user_context", {}),
    ))


@app.route("/api/mock/flight_search", methods=["POST"])
def api_mock_flight_search():
    b = request.get_json(force=True)
    return jsonify(tool_mock_search_flights(
        origin=b.get("origin", ""),
        destination=b.get("destination", ""),
        date=b.get("date", ""),
        budget=int(b.get("budget", 0) or 0),
        passengers=int(b.get("passengers", 1) or 1),
        cabin=b.get("cabin", "economy"),
        user_context=b.get("user_context", {}),
    ))


@app.route("/api/mock/monitor/start", methods=["POST"])
def api_mock_monitor_start():
    b = request.get_json(force=True)
    return jsonify(tool_mock_start_service_monitor(
        resource_type=b.get("resource_type", "queue"),
        target_name=b.get("target_name", ""),
        city=b.get("city", ""),
        condition=b.get("condition", ""),
        callback_action=b.get("callback_action", ""),
        duration_minutes=int(b.get("duration_minutes", 30) or 30),
        user_context=b.get("user_context", {}),
    ))


@app.route("/api/mock/monitor/<monitor_id>", methods=["GET"])
def api_mock_monitor_status(monitor_id):
    r = tool_mock_get_monitor_status(monitor_id)
    return (jsonify(r), 200 if r.get("success") else 404)


@app.route("/api/proxy_image", methods=["GET"])
def api_proxy_image():
    url = request.args.get("url", "").strip()
    if not url or not re.match(r"^https?://", url):
        return "", 400
    try:
        resp = requests.get(url, headers={"Referer": "https://meituan.com"}, timeout=REQUEST_TIMEOUT)
        resp.raise_for_status()
        return Response(resp.content, mimetype=resp.headers.get("content-type", "image/jpeg"))
    except Exception:
        return "", 404


def _fallback_trip_compare_plans(city: str, budget: int = 800) -> list:
    city = city or "目的地"
    return [
        {
            "persona_key": "relax",
            "label": "🍃 松弛慢游",
            "desc": "少景点、多停留、低强度",
            "budget_total": budget,
            "days": [{
                "day": 1, "theme": "松弛慢游",
                "route": ["集合/出发点", f"{city}核心景区", "街区咖啡", "傍晚慢逛"],
                "transport": "地铁 + 打车 + 步行",
                "budget": round(budget * 0.55),
                "tip": "节奏稳，覆盖点较少",
                "schedule": [
                    {"time":"09:30","type":"transit","activity":"集合/出发","duration_min":30},
                    {"time":"10:30","type":"sight","activity":f"{city}核心景区","duration_min":90},
                    {"time":"14:30","type":"rest","activity":"街区咖啡/休息","duration_min":70},
                    {"time":"17:30","type":"relax","activity":"傍晚慢逛","duration_min":80},
                ],
            }],
        },
        {
            "persona_key": "special_force",
            "label": "⚡ 特种兵模式",
            "desc": "多节点、高效率、压缩停留",
            "budget_total": budget + 120,
            "days": [{
                "day": 1, "theme": "高效率压缩",
                "route": ["集合/出发点", f"{city}核心景区", f"{city}地标", f"{city}夜景点"],
                "transport": "地铁 + 打车",
                "budget": round(budget * 0.62),
                "tip": "强度较高，适合体力好的人",
                "schedule": [
                    {"time":"08:30","type":"transit","activity":"集合/出发","duration_min":20},
                    {"time":"09:20","type":"sight","activity":f"{city}核心景区","duration_min":60},
                    {"time":"12:30","type":"sight","activity":f"{city}地标","duration_min":55},
                    {"time":"18:30","type":"relax","activity":f"{city}夜景点","duration_min":70},
                ],
            }],
        },
        {
            "persona_key": "foodie",
            "label": "🍜 美食脑袋",
            "desc": "餐饮优先，景点服务于吃饭动线",
            "budget_total": budget + 180,
            "days": [{
                "day": 1, "theme": "美食动线",
                "route": ["集合/出发点", "本地早餐", f"{city}核心景点", "夜市/本地菜餐厅"],
                "transport": "地铁 + 步行",
                "budget": round(budget * 0.6),
                "tip": "饭点可能排队，建议开启排队监控",
                "schedule": [
                    {"time":"09:30","type":"food","activity":"本地早餐","duration_min":50},
                    {"time":"11:00","type":"sight","activity":f"{city}核心景点","duration_min":80},
                    {"time":"14:00","type":"food","activity":"小吃/咖啡补给","duration_min":60},
                    {"time":"18:00","type":"food","activity":"夜市/本地菜餐厅","duration_min":90},
                ],
            }],
        },
    ]

@app.route("/api/trip_compare", methods=["POST", "OPTIONS"])
@app.route("/api/plan_variants", methods=["POST", "OPTIONS"])
def api_trip_compare():
    """生成3种人格方案供用户对比选择。"""
    if request.method == "OPTIONS":
        return jsonify({"ok": True})
    b = request.get_json(force=True, silent=True) or {}
    city = (b.get("city") or "上海").strip()
    user_prompt = (b.get("user_prompt") or b.get("prompt") or f"去{city}玩").strip()
    budget = _optional_int(b.get("budget"), None) or _extract_trip_requirements(user_prompt, city).get("budget", 800)

    # 3种对比人格：松弛 / 特种兵 / 美食脑袋
    compare_personas = [
        {"key": "relax",        "label": "🍃 松弛慢游",   "desc": "少景点多停留，保留大量弹性时间"},
        {"key": "special_force","label": "⚡ 特种兵模式", "desc": "高密度打卡，效率最大化"},
        {"key": "foodie",       "label": "🍜 美食脑袋",   "desc": "以美食为主线，景点顺路打卡"},
    ]

    def _build_one(persona_key: str) -> dict:
        try:
            pstate = _persona_state(persona_key)
            req = _extract_trip_requirements(user_prompt, city)
            req["budget"] = budget or req.get("budget", 800)
            dest = _resolve_place_info(req["destination"], city)
            budget = _adjust_budget_by_persona(_budget_breakdown(req["budget"], req["days"], 0), pstate)
            weather_r = _weather_aux(dest.get("name") or city)
            foods = _attach_item_coords(_independent_items("restaurant_search", dest.get("name", city), "本地菜小吃", {}, 4), dest.get("name", city))
            sights = _attach_item_coords(_independent_items("ticket_search", dest.get("name", city), "景点门票", {}, 4), dest.get("name", city))
            day_plan = _build_itinerary_days(
                dest.get("name", city), req["days"], sights, foods,
                "地铁/打车", budget, pstate, weather_r
            )
            return {
                "persona_key": persona_key,
                "days": day_plan,
                "budget_total": budget.get("total", req["budget"]),
                "weather": weather_r if weather_r.get("success") else None,
            }
        except Exception as e:
            return {"persona_key": persona_key, "error": str(e)}

    try:
        with ThreadPoolExecutor(max_workers=3) as pool:
            futures = {p["key"]: pool.submit(_build_one, p["key"]) for p in compare_personas}
            results = {}
            for key, fut in futures.items():
                try:
                    results[key] = fut.result(timeout=15)
                except Exception as e:
                    results[key] = {"persona_key": key, "error": _safe_error_text(e)}

        plans = []
        for p in compare_personas:
            r = results.get(p["key"], {})
            plans.append({
                "persona_key": p["key"],
                "label": p["label"],
                "desc": p["desc"],
                "days": r.get("days", []),
                "budget_total": r.get("budget_total", 0),
                "weather": r.get("weather"),
                "error": r.get("error"),
            })
        if not any(p.get("days") for p in plans):
            plans = _fallback_trip_compare_plans(city, budget)
        return jsonify({"success": True, "city": city, "plans": plans})
    except Exception as e:
        return jsonify({
            "success": True,
            "city": city,
            "plans": _fallback_trip_compare_plans(city, budget),
            "fallback": True,
            "message": f"主规划暂不可用，已切换三方案备用生成：{_safe_error_text(e)}",
        })


@app.route("/api/task-state", methods=["GET", "DELETE"])
def api_task_state():
    session_id = request.args.get("session_id", "default")
    if request.method == "DELETE":
        _clear_task_state(session_id)
        return jsonify({"success": True})
    return jsonify(_get_task_state(session_id))


@app.route("/api/reset", methods=["POST"])
def api_reset():
    """完整清空指定 session 的所有后端状态，配合前端生成新 session_id 使用。"""
    b = request.get_json(force=True) or {}
    session_id = b.get("session_id", "default")
    _clear_task_state(session_id)
    print(f"[RESET] session {session_id!r} cleared")
    return jsonify({"ok": True, "message": "session reset", "session_id": session_id})


@app.route("/api/agent", methods=["POST"])
def api_agent():
    b          = request.get_json(force=True)
    msg        = b.get("message","").strip()
    city       = b.get("city","上海").strip()
    raw_history= b.get("history", [])
    persona    = b.get("persona","").strip()
    personas   = b.get("personas", [])
    session_id = b.get("session_id", "default")
    action_type= b.get("action_type","").strip()
    option_id  = b.get("option_id","").strip()
    if isinstance(personas, list) and personas:
        merged = [persona] if persona else []
        merged.extend([str(x) for x in personas if x])
        persona = ",".join(dict.fromkeys([x for x in merged if x]))
    route_profile  = b.get("route_profile","").strip()
    route_strategy = b.get("route_strategy","").strip()
    map_provider   = b.get("map_provider","").strip()
    if not msg: return jsonify({"error":"message不能为空"}), 400

    # ── 要求10：详细调试日志 ────────────────────────────────────────
    ts_before = _get_task_state(session_id)
    _det_dest = re.search(_CITY_PAT, msg)
    _det_city_str = _det_dest.group(1) if _det_dest else None
    _is_fw = msg.strip() in _FOLLOWUP_SET
    _is_nt = _is_new_task(msg, ts_before)
    print(f"[AGENT] raw_message={msg!r}")
    print(f"[AGENT] detected_destination={_det_city_str!r} | is_new_task={_is_nt} | is_followup={_is_fw}")
    print(f"[AGENT] current_task_before: city={ts_before.get('active_city')!r} status={ts_before.get('status','idle')} goal={ts_before.get('last_user_goal','')[:40]!r}")

    # ══ 第一步：短输入解析器（在 LLM 之前） ══════════════════════
    resolved = resolve_short_reply(msg, ts_before, action_type, option_id)
    is_followup = resolved and resolved.get("type") == "followup_current_task"
    if resolved and not is_followup:
        result = _handle_resolved_action(resolved, ts_before, session_id)
        ts_after = _get_task_state(session_id)
        print(f"[AGENT] resolved={resolved['type']} ts_after_status={ts_after.get('status')}")
        def _quick_stream():
            reply = result.get("reply","")
            yield f"data: {json.dumps({'type':'final','text':reply,'task_state':ts_after}, ensure_ascii=False)}\n\n"
        return Response(stream_with_context(_quick_stream()), mimetype="text/event-stream")

    # ══ 第二步：新任务检测 ════════════════════════════════════════
    if _is_nt and not is_followup:
        _clear_task_state(session_id)
        print(f"[AGENT] new task detected, cleared state")

    # ══ 第三步：当前输入城市立即锁定到 task_state ════════════════
    ts_now = _get_task_state(session_id)
    if _det_city_str:
        _prev_city = ts_now.get("active_city", "")
        if _det_city_str != _prev_city:
            print(f"[AGENT] city lock: {_prev_city!r} → {_det_city_str!r}")
        ts_now = dict(ts_now)
        ts_now["active_city"] = _det_city_str
        ts_now["active_destination"] = _det_city_str
        if not ts_now.get("active_task_id"):
            ts_now["active_task_id"] = f"task_{uuid.uuid4().hex[:8]}"
        # 顺带提取预算/天数（要求1）
        _b_m = re.search(r"预算\s*([0-9]+)", msg)
        _d_m = re.search(r"([0-9一二两三四五六七八九十]{1,3})\s*天", msg)
        if _b_m:
            ts_now["active_budget"] = int(_b_m.group(1))
        if _d_m:
            ts_now["active_days"] = _zh_to_int(_d_m.group(1), 1)
        if persona:
            ts_now["active_persona"] = persona
        _set_task_state(session_id, ts_now)

    # ══ 第四步：构建干净历史（只含当前任务相关轮次） ════════════════
    history = _build_clean_history(raw_history, ts_now)

    # ══ 第五步：注入 CURRENT_TASK_LOCK 到 system_prompt ════════════
    # 无论状态是否 idle，只要有 active_city 就注入任务锁
    _lock_city = ts_now.get("active_city") or ts_now.get("active_destination", "")
    task_ctx = ""
    if _lock_city:
        opts = ts_now.get("last_options", [])
        opts_text = ("候选方案：" + "；".join(f"方案{o['index']+1}={o['label']}" for o in opts)) if opts else ""
        task_ctx = (
            f"\n\n## [CURRENT_TASK_LOCK] 活跃任务锁定\n"
            f"- 目的地（最高优先级，禁止被历史对话覆盖）: {_lock_city}\n"
            f"- 状态: {ts_now.get('status','idle')}\n"
            f"- 预算: {ts_now.get('active_budget','待定')}\n"
            f"- 天数: {ts_now.get('active_days','待定')}\n"
            f"- 意图: {ts_now.get('active_intent','出游规划')}\n"
            f"- 用户目标: {ts_now.get('last_user_goal','')[:80]}\n"
            f"- {opts_text}\n"
            f"[规则] 本次回复必须围绕目的地={_lock_city}展开。"
            f"如用户问\"查好了吗/继续/好了没\"等，必须继续{_lock_city}的规划。"
            f"禁止从历史记录中提取其他城市（如北京/重庆/新加坡）来替代当前任务。"
        )
        # 要求8：如果说"查好了吗/生成方案"且状态是planning，直接生成初版方案，不假装异步
        if is_followup and ts_now.get("status") == "planning":
            task_ctx += (
                f"\n[要求8] 用户正在跟进上一步规划。"
                f"请直接给出{_lock_city}的完整初版方案，"
                f"不要说'稍等'或'正在查'，直接输出行程时间线+预算+推荐。"
            )

    print(f"[AGENT] current_task_after: city={ts_now.get('active_city')!r} status={ts_now.get('status','idle')} lock_injected={bool(task_ctx)}")
    print(f"[AGENT] messages_sent_to_llm: history_turns={len([h for h in history if h.get('role')!='system'])} task_lock={bool(_lock_city)}")

    def _wrap_with_task_state(gen):
        for chunk in gen:
            if chunk.startswith("data: "):
                try:
                    evt = json.loads(chunk[6:])
                    if evt.get("type") == "final":
                        new_ts = _update_task_state_from_reply(session_id, msg, evt.get("text",""))
                        evt["task_state"] = new_ts
                        print(f"[AGENT] final ts_status={new_ts.get('status')} options={len(new_ts.get('last_options',[]))}")
                        yield f"data: {json.dumps(evt, ensure_ascii=False)}\n\n"
                        continue
                except Exception:
                    pass
            yield chunk

    base = run_deepseek_agent(msg, city, history, persona, route_profile,
                              route_strategy, map_provider, extra_system=task_ctx)
    return Response(stream_with_context(_wrap_with_task_state(base.response)),
                    mimetype="text/event-stream")


@app.route("/api/chat", methods=["POST"])
def api_chat():
    if not DEEPSEEK_API_KEY: return jsonify({"error":"请设置DEEPSEEK_API_KEY"}), 500
    b          = request.get_json(force=True)
    msg        = b.get("message","").strip()
    city       = b.get("city","上海").strip()
    raw_history= b.get("history", [])
    persona    = b.get("persona","").strip()
    route_profile  = b.get("route_profile","").strip()
    route_strategy = b.get("route_strategy","").strip()
    map_provider   = b.get("map_provider","").strip()
    session_id = b.get("session_id", "default")
    action_type= b.get("action_type","").strip()
    option_id  = b.get("option_id","").strip()
    if not msg: return jsonify({"error":"message不能为空"}), 400

    # ── 日志 ──────────────────────────────────────────────────
    ts_before = _get_task_state(session_id)
    print(f"[CHAT] raw={msg!r} action_type={action_type!r} option_id={option_id!r} "
          f"status={ts_before.get('status','idle')} session={session_id}")

    # ══ 第一步：短输入解析器（在 LLM 之前） ══════════════════════
    resolved = resolve_short_reply(msg, ts_before, action_type, option_id)
    _is_fw_chat = resolved and resolved.get("type") == "followup_current_task"
    if resolved and not _is_fw_chat:
        result = _handle_resolved_action(resolved, ts_before, session_id)
        if result is not None:
            ts_after = _get_task_state(session_id)
            print(f"[CHAT] resolved={resolved['type']} ts_after_status={ts_after.get('status')}")
            result["task_state"] = ts_after
            return jsonify(result)

    # ══ 第二步：新任务检测 ════════════════════════════════════════
    if _is_new_task(msg, ts_before) and not _is_fw_chat:
        _clear_task_state(session_id)

    # ══ 第三步：干净历史 ══════════════════════════════════════════
    ts_now  = _get_task_state(session_id)
    history = _build_clean_history(raw_history, ts_now)

    _update_soul_memory_from_message(msg)
    hdrs = {"Authorization":f"Bearer {DEEPSEEK_API_KEY}","Content-Type":"application/json"}

    # ══ 第四步：构建 Prompt ═══════════════════════════════════════
    task_ctx = ""
    if ts_now and ts_now.get("status") not in ("idle", None):
        opts = ts_now.get("last_options", [])
        opts_text = ("候选方案：" + "；".join(f"方案{o['index']+1}={o['label']}" for o in opts)) if opts else ""
        task_ctx = (
            f"\n\n## 当前任务状态（必须延续此任务）\n"
            f"- 状态: {ts_now.get('status','')}\n"
            f"- 城市: {ts_now.get('active_city','')}\n"
            f"- {opts_text}\n"
            f"- 用户目标: {ts_now.get('last_user_goal','')[:80]}\n"
        )
    system_prompt = (SYSTEM_PROMPT + "\n\n"
                     + _route_context(persona, route_profile, route_strategy)
                     + "\n\n" + _soul_context(msg) + task_ctx)
    msgs = [{"role":"system","content":system_prompt}]
    for h in history:
        if h.get("role") in ("user","assistant") and h.get("content"):
            msgs.append({"role":h["role"],"content":h["content"]})
    msgs.append({"role":"user","content":msg})

    final_reply = ""
    for _ in range(3):
        try:
            resp = requests.post(DEEPSEEK_URL, headers=hdrs, json={
                "model":DEEPSEEK_MODEL,"messages":msgs,"tools":AGENT_TOOLS,
                "tool_choice":"auto","max_tokens":1500,"temperature":0.3}, timeout=DEEPSEEK_TIMEOUT)
            resp.raise_for_status()
            res = resp.json()
        except Exception as e: return jsonify({"error":_safe_error_text(e)}), 500
        ch = res["choices"][0]; m = ch["message"]; fin = ch.get("finish_reason","")
        if fin == "stop":
            final_reply = _clean_markdown(m.get("content",""))
            break
        if m.get("tool_calls"):
            msgs.append(m)
            for tc in m["tool_calls"]:
                fn = tc["function"]["name"]
                fa = json.loads(tc["function"]["arguments"])
                if fn=="get_weather":             tr=tool_get_weather(fa.get("city",city))
                elif fn=="plan_meituan_trip":     tr=tool_plan_meituan_trip(fa.get("city",city),fa.get("user_prompt",msg),fa.get("persona",persona),fa.get("map_provider",map_provider))
                elif fn=="plan_panorama_trip":    tr=tool_plan_panorama_trip(fa.get("city",city),fa.get("user_prompt",msg),fa.get("origin",""),fa.get("destination",""),fa.get("persona",persona),fa.get("map_provider",map_provider))
                elif fn=="plan_weekend_trip":     tr=tool_plan_weekend_trip(fa.get("city",city),fa.get("user_prompt",msg),fa.get("persona",persona),fa.get("route_profile",route_profile),fa.get("map_provider",map_provider),float(fa.get("duration_hours",4) or 4))
                elif fn=="plan_route":            tr=tool_plan_route(fa.get("city",city),fa.get("start",""),fa.get("destination",""),fa.get("riding_type",0),_optional_int(fa.get("road_prefer")),fa.get("route_profile",route_profile),fa.get("persona",persona),fa.get("route_strategy",route_strategy))
                elif fn=="search_michelin":       tr=tool_search_michelin(fa.get("query",""))
                elif fn=="call_meituan_skill":    tr=tool_call_meituan_skill(fa.get("intent","restaurant_search"),fa.get("city",city),fa.get("keyword",""),fa.get("location",""),fa.get("user_lat"),fa.get("user_lng"),fa.get("filters",{}),int(fa.get("limit",5)))
                elif fn=="find_nearest_michelin": tr=tool_find_nearest_michelin(float(fa.get("lat",0)),float(fa.get("lng",0)))
                elif fn=="mock_request_ride":     tr=tool_mock_request_ride(fa.get("origin",""),fa.get("destination",""),fa.get("city",city),fa.get("trigger_reason",msg),fa.get("user_context",{}))
                elif fn=="mock_search_flights":   tr=tool_mock_search_flights(fa.get("origin",""),fa.get("destination",""),fa.get("date",""),int(fa.get("budget",0) or 0),int(fa.get("passengers",1) or 1),fa.get("cabin","economy"),fa.get("user_context",{}))
                elif fn=="mock_start_service_monitor": tr=tool_mock_start_service_monitor(fa.get("resource_type","queue"),fa.get("target_name",""),fa.get("city",city),fa.get("condition",msg),fa.get("callback_action",""),int(fa.get("duration_minutes",30) or 30),fa.get("user_context",{}))
                elif fn=="mock_get_monitor_status": tr=tool_mock_get_monitor_status(fa.get("monitor_id",""))
                elif fn=="create_pending_order":  tr=tool_create_pending_order(fa.get("order_type","unknown"),fa.get("item",{}),fa.get("user_context",{}))
                elif fn=="confirm_mock_order":    tr=tool_confirm_mock_order(fa.get("order_id",""))
                elif fn=="simulate_price_scenario": tr=tool_simulate_price_scenario(fa.get("event_type","normal"),fa.get("origin",""),fa.get("destination",""),fa.get("city",city))
                elif fn=="patch_plan_item":        tr=tool_patch_plan_item(fa.get("order_id",""),fa.get("item_type","hotel"),fa.get("reason",""),fa.get("persona",persona),fa.get("budget_max",0))
                else: tr={"error":"unknown"}
                msgs.append({"role":"tool","tool_call_id":tc["id"],"content":json.dumps(tr,ensure_ascii=False)})

    if not final_reply:
        try:
            resp2 = requests.post(DEEPSEEK_URL, headers=hdrs, json={
                "model":DEEPSEEK_MODEL,"messages":msgs,"max_tokens":1500,"temperature":0.3}, timeout=DEEPSEEK_TIMEOUT)
            resp2.raise_for_status()
            final_reply = _clean_markdown(resp2.json()["choices"][0]["message"].get("content","处理超时，请重试"))
        except Exception:
            final_reply = "处理超时，请重试"

    new_ts = _update_task_state_from_reply(session_id, msg, final_reply)
    print(f"[CHAT] final ts_status={new_ts.get('status')} options={len(new_ts.get('last_options',[]))}")
    return jsonify({"reply": final_reply, "task_state": new_ts})


def _baidu_translate(text: str, to_lang: str, from_lang: str = "auto") -> dict:
    """调用百度翻译 AI 接口，返回 {"text": ..., "from": ..., "to": ...} 或 {"error": ...}"""
    try:
        resp = requests.post(
            BAIDU_TRANSLATE_URL,
            headers={"Content-Type": "application/json", "Authorization": f"Bearer {BAIDU_TRANSLATE_KEY}"},
            json={"from": from_lang, "to": to_lang, "q": text},
            timeout=10,
        )
        data = resp.json()
        if "trans_result" in data:
            translated = "\n".join(r["dst"] for r in data["trans_result"])
            return {"text": translated, "from": data.get("from", from_lang), "to": data.get("to", to_lang)}
        return {"error": data.get("error_msg", "baidu_error"), "error_code": data.get("error_code"), "text": text}
    except Exception as e:
        return {"error": str(e), "text": text}


@app.route("/api/translate", methods=["POST"])
def api_translate():
    b = request.get_json(force=True)
    text = (b.get("text") or "").strip()
    target_lang = (b.get("target_lang") or "en").strip()
    from_lang   = (b.get("from_lang") or "auto").strip()
    if not text:
        return jsonify({"text": ""})
    result = _baidu_translate(text, target_lang, from_lang)
    if "error" in result and result.get("text") == text:
        return jsonify({"text": text, "error": result["error"], "fallback": True})
    return jsonify({"text": result["text"], "from": result.get("from"), "to": result.get("to")})


@app.route("/api/translate-batch", methods=["POST"])
def api_translate_batch():
    """批量翻译 UI 字符串列表，返回 {results: [...]}"""
    b = request.get_json(force=True)
    texts = b.get("texts") or []
    target_lang = (b.get("target_lang") or "en").strip()
    from_lang   = (b.get("from_lang") or "zh").strip()
    if not texts:
        return jsonify({"results": []})
    combined = "\n||||\n".join(str(t) for t in texts)
    result = _baidu_translate(combined, target_lang, from_lang)
    if "error" in result and result.get("text") == combined:
        return jsonify({"results": texts, "error": result["error"], "fallback": True})
    parts = result["text"].split("\n||||\n")
    while len(parts) < len(texts):
        parts.append(texts[len(parts)])
    return jsonify({"results": parts[:len(texts)], "from": result.get("from"), "to": result.get("to")})


@app.route("/api/history", methods=["GET", "POST", "DELETE"])
def api_history():
    if request.method == "DELETE":
        with _history_conn() as conn:
            conn.execute("DELETE FROM chat_messages")
            try:
                conn.execute("INSERT INTO chat_messages_fts(chat_messages_fts) VALUES('rebuild')")
            except Exception:
                pass
        return jsonify({"success": True})
    if request.method == "GET":
        q = request.args.get("q", "").strip()
        limit = _optional_int(request.args.get("limit"), 30) or 30
        return jsonify({"success": True, "items": _search_history(q, limit)})
    b = request.get_json(force=True)
    messages = b.get("messages")
    city = b.get("city", "")
    persona = b.get("persona", "")
    session_id = b.get("session_id", "default")
    lang = b.get("lang", "zh")
    saved = []
    if isinstance(messages, list):
        for msg in messages:
            if isinstance(msg, dict):
                item = _save_history_message(msg.get("role", "assistant"), msg.get("content", ""), city, persona, session_id, lang)
                if item:
                    saved.append(item)
    else:
        item = _save_history_message(b.get("role", "assistant"), b.get("content", ""), city, persona, session_id, lang)
        if item:
            saved.append(item)
    return jsonify({"success": True, "saved": saved})


@app.route("/api/soul", methods=["GET"])
def api_soul():
    profile = _load_soul_user_profile()
    return jsonify({
        "success": True,
        "summary": _soul_memory_summary(profile),
        "identity": _read_text_file(SOUL_IDENTITY_PATH),
        "memory_rules": _read_text_file(SOUL_MEMORY_RULES_PATH),
        "profile": profile,
    })


@app.route("/ask_michelin", methods=["POST"])
def ask_michelin_route():
    b = request.get_json(force=True)
    q = b.get("question","").strip()
    if not q: return jsonify({"error":"问题不能为空"}), 400
    r = tool_search_michelin(q)
    if r.get("success"):
        return jsonify({"answer":_clean_markdown(r.get("answer","")),"references":r.get("references",[]),"fallback":r.get("fallback",False)})
    return jsonify({"error":r.get("error","米其林查询失败")}), 500


# ✅ 新增：最近米其林 HTTP 接口（前端定位后直接调用）
@app.route("/api/nearest_michelin", methods=["POST"])
def api_nearest_michelin():
    b = request.get_json(force=True)
    lat = b.get("lat")
    lng = b.get("lng")
    if lat is None or lng is None:
        return jsonify({"error":"lat 和 lng 不能为空"}), 400
    limit = int(b.get("limit", 5))
    cuisine = b.get("cuisine_filter","")
    r = tool_find_nearest_michelin(float(lat), float(lng), limit, cuisine)
    if r.get("success"): return jsonify(r)
    return jsonify({"error":r.get("error")}), 500


@app.route("/api/health", methods=["GET"])
def health():
    gaode_key  = os.environ.get("GAODE_KEY","")
    meituan_key= os.environ.get("MEITUAN_API_KEY","")
    return jsonify({
        "status":"ok","version":"3.8",
        "weather":   "Open-Meteo（全球）",
        "route":     "全景出行判定 + 百度地图 + 人格路线画像 fast/scenic/quiet/budget",
        "panorama_agent": "跨国/跨省/跨城 Tool（飞机/高铁/自驾/地铁/打车/步行自动判定；骑行需用户明确提出）✅",
        "meituan_trip_agent": "行程/预算/酒店 Tool（规则路由+并发美团酒店/美食/景点+天气辅助）✅",
        "hermes_skill": _hermes_skill_status(),
        "soul": {
            "enabled": True,
            "dir": SOUL_DIR,
            "summary": _soul_memory_summary(),
        },
        "pending_orders": len(PENDING_ORDERS),
        "mock_resources": {
            "ride_hailing": "待确认打车订单 ✅",
            "flight_ticket": "待确认机票订单 ✅",
            "async_monitor": f"后台资源监控 ✅（当前{len(MOCK_RESOURCE_MONITORS)}个）",
        },
        "weekend_agent": "周末出行 Tool（真实路线优先+活动+地图+智能兜底）✅",
        "ai":        f"DeepSeek ({'✅已配置' if DEEPSEEK_API_KEY else '❌未配置'})",
        "rag":       f"米其林RAG ({'✅' if MICHELIN_AVAILABLE else '⚠️RAG不可用，CSV兜底可用'})",
        "nearest":   "最近米其林 Haversine ✅",
        "meituan":   f"美团开放平台 ({'✅已配置 MEITUAN_API_KEY' if meituan_key else '⚠️未配置（需申请）'})",
        "meituan_skills": _meituan_skill_status(),
        "gaode":     f"高德POI ({'✅已配置 GAODE_KEY' if gaode_key else '⚠️未配置（免费申请）'})",
        "meituan_tools": len(_MEITUAN_TOOLS),
        "route_profiles": ROUTE_PROFILES,
        "persona_profiles": PERSONA_PROFILES,
    })


if __name__ == "__main__":
    print("="*55)
    print("🍊 马到橙功后端 v3.8 启动")
    print(f"   DeepSeek : {'✅ 已配置' if DEEPSEEK_API_KEY else '❌ 请设置DEEPSEEK_API_KEY'}")
    print(f"   米其林RAG: {'✅ 初始化中（后台加载）' if MICHELIN_AVAILABLE else '⚠️  RAG不可用，启用CSV兜底'}")
    print("   最近米其林: ✅ Haversine 地理索引")
    mt_count = len(_MEITUAN_TOOLS)
    print(f"   美团 Skill : {'✅ 已加载 '+str(mt_count)+'个工具' if mt_count else '⚠️  meituan_skill_tool.json 未找到'}")
    print("   多轮对话 : ✅ 最近12轮记忆")
    print(f"   Soul管家 : ✅ {_soul_memory_summary()}")
    print("   人格路线 : ✅ Agent自动推荐 + 用户可切换")
    print("   全景出行 : ✅ 跨国/跨省/跨城自动判定交通方式")
    print("   周末Agent: ✅ 真实路线优先 + 活动规划 + 三地图链接 + 智能兜底")
    print("   美团行程 : ✅ 规则路由 + 预算闭环 + 酒店/美食/景点并发匹配")
    gaode_k  = os.environ.get("GAODE_KEY","")
    mt_api_k = os.environ.get("MEITUAN_API_KEY","")
    print(f"   高德POI  : {'✅ 已配置' if gaode_k else '⚠️  export GAODE_KEY=xxx（免费）'}")
    print(f"   美团API  : {'✅ 已配置' if mt_api_k else '⚠️  export MEITUAN_API_KEY=xxx（需申请）'}")
    print("="*55)
    app.run(
        host="0.0.0.0",
        port=5000,
        debug=False,
        threaded=True,
        use_reloader=False,
    )
