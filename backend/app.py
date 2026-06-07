"""
马到橙功后端 v3.8
新增：美团行程闭环 Tool + 全景出行 Agent Tool + 周末出行 Agent Tool + 人格路线画像 + 最近米其林 + 多轮对话记忆
天气：Open-Meteo · 路线：百度/高德地图 · AI：DeepSeek/LongCat · RAG：米其林 ChromaDB
"""
import csv, json, os, threading, math, re, shutil, subprocess, sys, sqlite3, time, uuid, random, hashlib, unicodedata
from concurrent.futures import ThreadPoolExecutor, TimeoutError as FuturesTimeout
from typing import Optional
from urllib.parse import quote
import requests
from flask import Flask, Response, jsonify, request, stream_with_context
from flask_cors import CORS

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
_HTTP_SESSION = requests.Session()
_HTTP_ADAPTER = requests.adapters.HTTPAdapter(pool_connections=12, pool_maxsize=24, max_retries=0)
_HTTP_SESSION.mount("https://", _HTTP_ADAPTER)
_HTTP_SESSION.mount("http://", _HTTP_ADAPTER)

def _load_local_env(path: str) -> None:
    """Load local .env values without adding a dependency; never overwrite shell env."""
    if not os.path.exists(path):
        return
    try:
        with open(path, "r", encoding="utf-8") as f:
            for line in f:
                s = line.strip()
                if not s or s.startswith("#") or "=" not in s:
                    continue
                k, v = s.split("=", 1)
                k = k.strip()
                v = v.strip().strip('"').strip("'")
                if k and k not in os.environ:
                    os.environ[k] = v
    except Exception as e:
        print(f"⚠️  本地环境变量加载失败：{_safe_error_text(e) if '_safe_error_text' in globals() else e}")

_load_local_env(os.path.join(BASE_DIR, ".env"))

def _load_amap_webservice_key_from_skill_config() -> str:
    """Read OpenClaw AMap LBS skill config when Flask env is not configured."""
    candidates = [
        os.path.join(BASE_DIR, "amap-lbs-skill", "config.json"),
        os.path.expanduser("~/.openclaw/workspace/skills/amap-lbs-skill/config.json"),
    ]
    for path in candidates:
        try:
            if not os.path.exists(path):
                continue
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            key = str(data.get("webServiceKey") or data.get("key") or "").strip()
            if key and key != "your_amap_webservice_key_here":
                print(f"✅ 已读取高德 Skill WebService 配置：{path}")
                return key
        except Exception as e:
            print(f"⚠️  高德 Skill 配置读取失败：{e}")
    return ""

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

BAIDU_AK          = os.environ.get("BAIDU_SERVER_AK", os.environ.get("BAIDU_MAP_AK", "8tskCa9dm3m8i1DQvtPRW9AxSfB1cZKY"))
BAIDU_RIDING_URL  = "https://api.map.baidu.com/directionlite/v1/riding"
BAIDU_WALKING_URL = "https://api.map.baidu.com/directionlite/v1/walking"
BAIDU_GEOCODE_URL = "https://api.map.baidu.com/geocoding/v3/"
BAIDU_PLACE_URL   = "https://api.map.baidu.com/place/v2/search"
OM_GEO_URL        = "https://geocoding-api.open-meteo.com/v1/search"
OM_WEATHER_URL    = "https://api.open-meteo.com/v1/forecast"
DEEPSEEK_API_KEY  = os.environ.get("DEEPSEEK_API_KEY", "")
DEEPSEEK_URL      = "https://api.deepseek.com/chat/completions"
DEEPSEEK_MODEL    = "deepseek-chat"
LONGCAT_API_KEY   = os.environ.get("LONGCAT_API_KEY", "")
LONGCAT_URL       = os.environ.get("LONGCAT_URL", "https://api.longcat.chat/openai/v1/chat/completions")
LONGCAT_MODEL     = os.environ.get("LONGCAT_MODEL", "LongCat-2.0-Preview")
LLM_PROVIDER      = os.environ.get("MADO_LLM_PROVIDER", "auto").strip().lower()
LONGCAT_RESOURCE_TIMEOUT = int(os.environ.get("LONGCAT_RESOURCE_TIMEOUT", "5"))
BAIDU_TRANSLATE_URL = "https://fanyi-api.baidu.com/ait/api/aiTextTranslate"
BAIDU_TRANSLATE_KEY = os.environ.get("BAIDU_TRANSLATE_KEY", "leVv_d8cn9iia4eo5ucr6cjp0")
AMAP_JSAPI_KEY = os.environ.get("AMAP_JSAPI_KEY", os.environ.get("GAODE_JSAPI_KEY", ""))
AMAP_SECURITY_JS_CODE = os.environ.get("AMAP_SECURITY_JS_CODE", os.environ.get("GAODE_SECURITY_JS_CODE", ""))
AMAP_MCP_KEY = os.environ.get("AMAP_MCP_KEY", os.environ.get("GAODE_MCP_KEY", ""))
AMAP_SERVICE_HOST = os.environ.get("AMAP_SERVICE_HOST", "")
BAIDU_BROWSER_AK = os.environ.get("BAIDU_BROWSER_AK", "")
EXPOSE_MAP_JS_KEYS = os.environ.get("EXPOSE_MAP_JS_KEYS", "1").strip().lower() not in ("0", "false", "no")
AMAP_WEBSERVICE_KEY = (
    os.environ.get("AMAP_WEBSERVICE_KEY")
    or os.environ.get("GAODE_KEY")
    or _load_amap_webservice_key_from_skill_config()
)
AMAP_GEOCODE_URL = "https://restapi.amap.com/v3/geocode/geo"
AMAP_PLACE_TEXT_URL = "https://restapi.amap.com/v3/place/text"
AMAP_PLACE_AROUND_URL = "https://restapi.amap.com/v3/place/around"
# 高德没有独立"厕所"POI，但商场/地铁站/加油站/公园/快餐这些场所内部通常有卫生间。
# 用周边类型搜索把它们当成"派生厕所点"。注意类型码用的是高德官方分类，与口口相传的码略有出入。
AMAP_TOILET_SUPPORT_TYPES = {
    "060000": "商场",      # 购物服务（含商场/购物中心）
    "150500": "地铁站",    # 地铁站
    "010100": "加油站",    # 加油站
    "110100": "公园",      # 公园广场
    "050300": "餐饮中心",  # 快餐厅
}
AMAP_ROUTE_URLS = {
    "walking": "https://restapi.amap.com/v3/direction/walking",
    "driving": "https://restapi.amap.com/v3/direction/driving",
    "riding": "https://restapi.amap.com/v4/direction/bicycling",
    "transit": "https://restapi.amap.com/v3/direction/transit/integrated",
}
CSV_PATH          = os.path.join(BASE_DIR, "rag_documents.csv")
BLACK_PEARL_PDF_PATH = os.environ.get(
    "BLACK_PEARL_PDF_PATH",
    os.path.join(os.path.dirname(BASE_DIR), "黑珍珠-米其林.pdf"),
)
BLACK_PEARL_SINGAPORE_XLSX_PATH = os.environ.get(
    "BLACK_PEARL_SINGAPORE_XLSX_PATH",
    os.path.join(os.path.dirname(BASE_DIR), "黑珍珠-rag数据-新加坡.xlsx"),
)
REQUEST_TIMEOUT   = int(os.environ.get("REQUEST_TIMEOUT", "6"))   # 高德/天气/POI：6s 上限，超时走兜底
DEEPSEEK_TIMEOUT  = int(os.environ.get("DEEPSEEK_TIMEOUT", "18"))  # route_map_json 生成质量优先；其它工具超时已收紧
AGENT_FINAL_BUDGET_SECONDS = float(os.environ.get("AGENT_FINAL_BUDGET_SECONDS", "8.5"))
ROUTE_JSON_FAST_TIMEOUT = float(os.environ.get("ROUTE_JSON_FAST_TIMEOUT", "3.0"))
# 真实 route_map_json 由 DeepSeek 生成；禁止退化展示 fast_route_card 模板。
# 用户可等待正式路线卡，超时只提示重试，不展示模板路线。
ROUTE_JSON_QUALITY_TIMEOUT = float(os.environ.get("ROUTE_JSON_QUALITY_TIMEOUT", "16"))
ENABLE_FOREGROUND_AMAP_ROUTE = os.environ.get("ENABLE_FOREGROUND_AMAP_ROUTE", "0") == "1"
MEITUAN_SKILL_TIMEOUT = int(os.environ.get("MEITUAN_SKILL_TIMEOUT", "25"))  # 美团 Skill CLI(mttravel 实测约18s)：25s 上限，超时才切备用
MEITUAN_FOREGROUND_TIMEOUT = int(os.environ.get("MEITUAN_FOREGROUND_TIMEOUT", "3"))  # 明确美团意图时：主流程最多等 3s，超时先出方案、后台继续补充
MEITUAN_BACKGROUND_TIMEOUT = int(os.environ.get("MEITUAN_BACKGROUND_TIMEOUT", "25"))  # 美团真实资源后台补充：最多等 25s(与 CLI 超时对齐，mttravel ~18-22s)，仍无则切备用
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
TOOL_TRACE_LOCK = threading.Lock()
RECENT_TOOL_CALLS = []

def _record_tool_call(tool: str, status: str = "success", elapsed_ms: int = 0, **meta) -> dict:
    """记录最近工具链，避免泄漏任何 Key，只保留调试所需摘要。"""
    item = {
        "tool": tool,
        "status": status,
        "elapsed_ms": int(elapsed_ms or 0),
        "ts": int(time.time()),
    }
    for k, v in (meta or {}).items():
        if k.lower() in {"key", "ak", "api_key", "token", "secret", "security_js_code"}:
            continue
        if isinstance(v, (str, int, float, bool)) or v is None:
            item[k] = v
    with TOOL_TRACE_LOCK:
        RECENT_TOOL_CALLS.append(item)
        del RECENT_TOOL_CALLS[:-40]
    return item

def _recent_tool_calls() -> list:
    with TOOL_TRACE_LOCK:
        return list(RECENT_TOOL_CALLS[-20:])

def _debug_tool_chain() -> list:
    with TOOL_TRACE_LOCK:
        calls = list(RECENT_TOOL_CALLS)
    order = ["deepseek", "longcat", "longcat_resource", "meituan_skill", "amap_poi", "amap_travel_planner", "amap_route", "amap_map_link", "deepseek_route_json", "mock_monitor", "mock_order"]
    defaults = {
        "deepseek": {"tool": "deepseek", "status": "idle"},
        "longcat": {"tool": "longcat", "status": "idle"},
        "longcat_resource": {"tool": "longcat_resource", "status": "idle"},
        "meituan_skill": {"tool": "meituan_skill", "status": "idle"},
        "amap_poi": {"tool": "amap_poi", "status": "idle"},
        "amap_travel_planner": {"tool": "amap_travel_planner", "status": "idle"},
        "amap_route": {"tool": "amap_route", "status": "idle"},
        "amap_map_link": {"tool": "amap_map_link", "status": "idle"},
        "deepseek_route_json": {"tool": "deepseek_route_json", "status": "idle"},
        "mock_monitor": {"tool": "mock_monitor", "status": "idle"},
        "mock_order": {"tool": "mock_order", "status": "ready"},
    }
    latest = {}
    for item in calls:
        latest[item.get("tool")] = item
    return [latest.get(tool, defaults[tool]) for tool in order]

def _has_any_llm() -> bool:
    return bool(DEEPSEEK_API_KEY or LONGCAT_API_KEY)

def _llm_provider_order() -> list:
    if LLM_PROVIDER in ("deepseek", "ds"):
        return ["deepseek", "longcat"]
    if LLM_PROVIDER in ("longcat", "longcat-api", "dragoncat", "longmao", "龙猫"):
        return ["longcat", "deepseek"]
    return ["deepseek", "longcat"]

def _llm_provider_config(provider: str) -> dict:
    if provider == "longcat":
        return {
            "tool": "longcat",
            "name": "LongCat",
            "api_key": LONGCAT_API_KEY,
            "url": LONGCAT_URL,
            "model": LONGCAT_MODEL,
        }
    return {
        "tool": "deepseek",
        "name": "DeepSeek",
        "api_key": DEEPSEEK_API_KEY,
        "url": DEEPSEEK_URL,
        "model": DEEPSEEK_MODEL,
    }

def _llm_status_text() -> str:
    parts = [
        f"DeepSeek ({'✅已配置' if DEEPSEEK_API_KEY else '❌未配置'})",
        f"LongCat/龙猫 ({'✅已配置' if LONGCAT_API_KEY else '❌未配置'})",
    ]
    if LLM_PROVIDER and LLM_PROVIDER != "auto":
        parts.append(f"优先：{LLM_PROVIDER}")
    return " / ".join(parts)

class _CollectedLLMResponse:
    def __init__(self, data: dict):
        self._data = data

    def json(self):
        return self._data

    def raise_for_status(self):
        return None

def _log_llm_usage(data: dict, provider: str, purpose: str, elapsed_ms: int, first_token_ms: int = None) -> None:
    usage = data.get("usage") or {}
    hit = usage.get("prompt_cache_hit_tokens")
    miss = usage.get("prompt_cache_miss_tokens")
    completion = usage.get("completion_tokens")
    prompt = usage.get("prompt_tokens")
    if hit is not None or miss is not None or first_token_ms is not None:
        print(
            f"[LLM_USAGE] provider={provider} purpose={purpose or '-'} "
            f"elapsed_ms={elapsed_ms} first_token_ms={first_token_ms if first_token_ms is not None else '-'} "
            f"prompt_tokens={prompt if prompt is not None else '-'} completion_tokens={completion if completion is not None else '-'} "
            f"prompt_cache_hit_tokens={hit if hit is not None else '-'} prompt_cache_miss_tokens={miss if miss is not None else '-'}"
        )

def _collect_streaming_chat_completion(url: str, headers: dict, body: dict, timeout_seconds: float) -> tuple[dict, int]:
    chunks = []
    usage = {}
    first_token_ms = None
    t0 = time.perf_counter()
    stream_body = dict(body)
    stream_body["stream"] = True
    stream_body.setdefault("stream_options", {"include_usage": True})
    with _HTTP_SESSION.post(url, headers=headers, json=stream_body, timeout=timeout_seconds, stream=True) as resp:
        resp.raise_for_status()
        for raw in resp.iter_lines(decode_unicode=True):
            if not raw:
                continue
            line = raw.strip()
            if line.startswith("data:"):
                line = line[5:].strip()
            if not line or line == "[DONE]":
                continue
            try:
                obj = json.loads(line)
            except Exception:
                continue
            if isinstance(obj.get("usage"), dict):
                usage = obj.get("usage") or usage
            choice = (obj.get("choices") or [{}])[0]
            delta = choice.get("delta") or {}
            piece = delta.get("content") or choice.get("text") or ""
            if piece:
                if first_token_ms is None:
                    first_token_ms = round((time.perf_counter() - t0) * 1000)
                chunks.append(piece)
    data = {"choices": [{"message": {"content": "".join(chunks)}}], "usage": usage}
    return data, first_token_ms

def _llm_chat_completion(payload: dict, purpose: str = "", timeout_seconds: float = None) -> requests.Response:
    """OpenAI-compatible chat completion router. Never logs secrets."""
    if not isinstance(payload, dict):
        raise ValueError("payload must be dict")
    last_error = None
    stream_collect = bool(payload.get("_stream_collect"))
    for provider in _llm_provider_order():
        cfg = _llm_provider_config(provider)
        if not cfg["api_key"]:
            continue
        body = dict(payload)
        body.pop("_stream_collect", None)
        body["model"] = cfg["model"]
        headers = {
            "Authorization": f"Bearer {cfg['api_key']}",
            "Content-Type": "application/json",
            "Connection": "keep-alive",
        }
        t0 = time.perf_counter()
        try:
            if stream_collect:
                try:
                    data, first_token_ms = _collect_streaming_chat_completion(
                        cfg["url"], headers, body, timeout_seconds or DEEPSEEK_TIMEOUT
                    )
                    elapsed = round((time.perf_counter() - t0) * 1000)
                    _record_tool_call(cfg["tool"], "success", elapsed,
                                      model=cfg["model"], provider=cfg["name"], purpose=purpose, stream=True)
                    _log_llm_usage(data, cfg["name"], purpose, elapsed, first_token_ms)
                    return _CollectedLLMResponse(data)
                except Exception as stream_error:
                    print(f"[LLM_STREAM_FALLBACK] provider={cfg['name']} purpose={purpose or '-'} error={_safe_error_text(stream_error)[:120] if '_safe_error_text' in globals() else type(stream_error).__name__}")
            resp = _HTTP_SESSION.post(cfg["url"], headers=headers, json=body, timeout=timeout_seconds or DEEPSEEK_TIMEOUT)
            resp.raise_for_status()
            elapsed = round((time.perf_counter() - t0) * 1000)
            try:
                _log_llm_usage(resp.json(), cfg["name"], purpose, elapsed)
            except Exception:
                pass
            _record_tool_call(cfg["tool"], "success", elapsed,
                              model=cfg["model"], provider=cfg["name"], purpose=purpose)
            return resp
        except Exception as e:
            last_error = e
            _record_tool_call(cfg["tool"], "timeout" if "timeout" in str(e).lower() else "error",
                              round((time.perf_counter() - t0) * 1000),
                              model=cfg["model"], provider=cfg["name"], purpose=purpose,
                              error=_safe_error_text(e)[:120] if "_safe_error_text" in globals() else type(e).__name__)
            continue
    if last_error:
        raise RuntimeError(_safe_error_text(last_error) if "_safe_error_text" in globals() else str(last_error)) from last_error
    raise RuntimeError("请设置 DEEPSEEK_API_KEY 或 LONGCAT_API_KEY")

def tool_call_longcat_resource_search(city: str, user_prompt: str,
                                      resource_types: list = None,
                                      limit: int = 8) -> dict:
    """
    美团龙猫资源意图层：只生成搜索策略和关键词，不伪造真实商户。
    真实店名仍以美团 Skill / 高德 POI 的返回为准。
    """
    city = (city or "").strip()
    resource_types = resource_types or ["restaurant", "sight", "hotel", "groupbuy"]
    t0 = time.perf_counter()
    if not LONGCAT_API_KEY:
        elapsed = round((time.perf_counter() - t0) * 1000)
        _record_tool_call("longcat_resource", "skipped", elapsed, city=city, purpose="resource_search")
        return {
            "success": False,
            "data_source": "longcat",
            "tool_name": "longcat-resource-agent",
            "elapsed_ms": elapsed,
            "message": "美团龙猫未配置，已切换美团 Skill / 高德 POI",
            "keywords": {},
            "resource_intent": {},
        }
    messages = [
        {
            "role": "system",
            "content": (
                "你是美团龙猫资源搜索规划器。只输出严格 JSON。"
                "你不能伪造具体商户名，只能根据用户意图生成本地生活资源类型、搜索关键词、排序策略和风控条件。"
                "JSON字段：resource_intent, keywords, ranking_rules, risk_controls, notes。"
            ),
        },
        {
            "role": "user",
            "content": json.dumps({
                "city": city,
                "user_prompt": user_prompt,
                "resource_types": resource_types,
                "limit": limit,
                "rules": [
                    "餐饮/酒店/景点/团购资源优先服务美团生态",
                    "不输出具体店名，真实店名由美团 Skill 或高德 POI 返回",
                    "考虑预算、排队、距离、评分、用户人格",
                ],
            }, ensure_ascii=False),
        },
    ]
    try:
        resp = _HTTP_SESSION.post(
            LONGCAT_URL,
            headers={"Authorization": f"Bearer {LONGCAT_API_KEY}", "Content-Type": "application/json", "Connection": "keep-alive"},
            json={"model": LONGCAT_MODEL, "messages": messages, "max_tokens": 800, "temperature": 0.2},
            timeout=LONGCAT_RESOURCE_TIMEOUT,
        )
        resp.raise_for_status()
        text = _clean_markdown(resp.json().get("choices", [{}])[0].get("message", {}).get("content", ""))
        obj = {}
        try:
            start, end = text.find("{"), text.rfind("}")
            obj = json.loads(text[start:end + 1] if start >= 0 and end > start else text)
        except Exception:
            obj = {}
        elapsed = round((time.perf_counter() - t0) * 1000)
        keywords = obj.get("keywords") if isinstance(obj.get("keywords"), dict) else {}
        if not keywords:
            keywords = {
                "restaurant": ["本地菜", "小吃", "不排队"],
                "sight": ["景点", "拍照", "夜景"],
                "hotel": ["酒店", "交通方便"],
                "groupbuy": ["团购", "优惠"],
            }
        result = {
            "success": True,
            "data_source": "longcat",
            "tool_name": "longcat-resource-agent",
            "elapsed_ms": elapsed,
            "city": city,
            "resource_intent": obj.get("resource_intent", {}),
            "keywords": keywords,
            "ranking_rules": obj.get("ranking_rules", ["预算优先", "距离优先", "评分优先", "排队风险低优先"]),
            "risk_controls": obj.get("risk_controls", ["排队超过20分钟切换同区域备选"]),
            "notes": obj.get("notes", []),
            "message": "美团龙猫已完成资源意图和关键词排序",
        }
        _record_tool_call("longcat_resource", "success", elapsed, city=city, purpose="resource_search")
        return result
    except Exception as e:
        elapsed = round((time.perf_counter() - t0) * 1000)
        status = "timeout" if "timeout" in str(e).lower() or "timed out" in str(e).lower() else "error"
        _record_tool_call("longcat_resource", status, elapsed, city=city, purpose="resource_search", error=_safe_error_text(e)[:120])
        return {
            "success": False,
            "data_source": "longcat",
            "tool_name": "longcat-resource-agent",
            "elapsed_ms": elapsed,
            "city": city,
            "message": "美团龙猫暂不可用，已切换美团 Skill / 高德 POI",
            "error": _safe_error_text(e),
            "keywords": {},
            "resource_intent": {},
        }

def _log_amap(kind: str, success: bool, elapsed_ms: int = 0, **meta) -> None:
    tool = {
        "AMAP_GEOCODE": "amap_geocode",
        "AMAP_POI": "amap_poi",
        "AMAP_TRAVEL_PLANNER": "amap_travel_planner",
        "AMAP_ROUTE": "amap_route",
        "AMAP_MAP_LINK": "amap_map_link",
    }.get(kind, "amap")
    status = "success" if success else "error"
    safe_meta = {k: v for k, v in (meta or {}).items() if k.lower() not in {"key", "ak", "api_key", "token", "secret", "security_js_code"}}
    log_tail = " ".join([f"{k}={v}" for k, v in safe_meta.items() if v not in ("", None)])
    print(f"[{kind}] status={status} elapsed_ms={int(elapsed_ms or 0)} {log_tail}".strip())
    _record_tool_call(tool, status, elapsed_ms, **safe_meta)

def _amap_meta(success: bool, elapsed_ms: int = 0, route_source: str = "") -> dict:
    out = {
        "data_source": "amap",
        "tool_name": "amap-lbs-skill",
        "success": bool(success),
        "elapsed_ms": int(elapsed_ms or 0),
    }
    if route_source:
        out["route_source"] = route_source
    return out

AMAP_LAST_ERROR = {"info": "", "message": ""}

# 高德 Key 类型错误/无效/额度超限属于「持久性故障」：首个调用失败即熔断，
# 避免一次规划里十几个高德调用串行各等 1-2s（实测会拖到 ~20-28s）。
AMAP_CIRCUIT_PERSISTENT_CODES = {
    "USERKEY_PLAT_NOMATCH", "INVALID_USER_KEY", "USERKEY_INVALID",
    "DAILY_QUERY_OVER_LIMIT", "CUQPS_HAS_EXCEEDED_THE_LIMIT", "missing_key",
}
AMAP_CIRCUIT_TTL = int(os.environ.get("AMAP_CIRCUIT_TTL", "300"))  # 熔断保持秒数；期间高德调用直接跳过走兜底，成功一次即复位
_AMAP_CIRCUIT = {"open_until": 0.0, "reason": ""}

def _amap_circuit_open() -> bool:
    return time.time() < _AMAP_CIRCUIT["open_until"]

def _trip_amap_circuit(reason: str) -> None:
    if not _amap_circuit_open():
        print(f"🟡 [AMAP_CIRCUIT] 高德持久性故障({reason})，{AMAP_CIRCUIT_TTL}s 内跳过高德调用，直接走美团/RAG/Mock 兜底")
    _AMAP_CIRCUIT.update({"open_until": time.time() + AMAP_CIRCUIT_TTL, "reason": str(reason or "")})

def _reset_amap_circuit() -> None:
    _AMAP_CIRCUIT.update({"open_until": 0.0, "reason": ""})

def _amap_user_message(info: str) -> str:
    return MAP_ROUTE_FRIENDLY_FALLBACK

def _remember_amap_error(info: str) -> str:
    msg = _amap_user_message(info)
    AMAP_LAST_ERROR.update({"info": str(info or ""), "message": msg})
    if str(info or "").strip() in AMAP_CIRCUIT_PERSISTENT_CODES:
        _trip_amap_circuit(info)
    return msg

def _clear_amap_error() -> None:
    AMAP_LAST_ERROR.update({"info": "", "message": ""})
    _reset_amap_circuit()

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
_RESET_ONLY_SET = {"重置", "清空", "重新开始", "换个话题", "取消当前任务"}

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
_CITY_PAT = (r"(福建省宁德市福鼎市|福建福鼎|宁德福鼎|福鼎市|福鼎|宁德|广东封开|封开|河北承德|承德|北京|上海|杭州|广州|深圳|成都|重庆|西安|武汉|南京|苏州"
             r"|新加坡|厦门|漳州|泉州|北海|桂林|南宁|三亚|香港|澳门|天津|青岛|大连|长沙|哈尔滨|沈阳)")
_NEW_TASK_PAT = re.compile(
    r"我想去.{1,10}(?:玩|旅游|看看|走走)|重新开始|换个话题|新规划|取消当前"
)

def _is_reset_only_message(text: str) -> bool:
    s = re.sub(r"[，。！？,;；\s]+", "", str(text or "").strip())
    return s in _RESET_ONLY_SET

def is_pure_reset_command(message: str) -> bool:
    return _is_reset_only_message(message)

def detect_new_destination(message: str) -> str:
    return _detect_message_destination(message)

def extract_city_from_message(message: str) -> str:
    """本轮用户文本里的城市最高优先级，避免历史/表单默认值覆盖新目的地。"""
    return detect_new_destination(message)

def detect_new_task(message: str) -> bool:
    """用户本轮已经给出目的地/规划意图时，静默切换到新任务并继续规划。"""
    s = str(message or "").strip()
    if not s or is_pure_reset_command(s):
        return False
    if detect_new_destination(s) and re.search(
        r"我想去|帮我规划|去.+玩|到.+玩|前往|一日游|两日游|三日游|周末去|从.+(?:去|到|前往)|行程|规划|攻略|旅游|旅行|游玩",
        s,
    ):
        return True
    return bool(re.search(
        r"(?:我想去|帮我规划|周末去|去|到|前往)\s*[^#，。！？,;；\s]{2,12}"
        r"(?:玩|旅游|旅行|游玩|一日游|两日游|三日游|行程|规划|攻略|$)"
        r"|从\s*[^#，。！？,;；\s]{2,12}\s*(?:去|到|前往)\s*[^#，。！？,;；\s]{2,12}",
        s,
    ))

def create_task_from_intent(session_id: str, intent: dict) -> dict:
    state = {
        "active_task_id": f"task_{uuid.uuid4().hex[:8]}",
        "status": "planning",
        "active_city": intent.get("destination", ""),
        "active_destination": intent.get("destination", ""),
        "city": intent.get("destination", ""),
        "destination": intent.get("destination", ""),
        "active_budget": intent.get("budget"),
        "active_days": intent.get("days"),
        "active_persona": intent.get("persona", ""),
        "active_intent": intent.get("intent", "trip_planning"),
        "last_user_goal": intent.get("raw", "")[:120],
    }
    _set_task_state(session_id, state)
    return state

def _is_new_destination_task(message: str, detected_city: str) -> bool:
    if not detected_city:
        return False
    return bool(re.search(r"去|到|前往|玩|旅游|旅行|游玩|行程|规划|攻略|安排|周末|一日|两日|三日|[0-9一二两三四五六七八九十]{1,3}\s*天", str(message or "")))

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
    new_city = _detect_message_destination(user_msg)
    if new_city:
        state["active_city"] = new_city
        state["active_destination"] = new_city
        state["city"] = new_city
        state["destination"] = new_city
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
WEATHER_CACHE = {}
WEATHER_CACHE_LOCK = threading.Lock()
WEATHER_CACHE_TTL_SECONDS = int(os.environ.get("WEATHER_CACHE_TTL_SECONDS", "1800"))
WEATHER_CACHE_STALE_SECONDS = int(os.environ.get("WEATHER_CACHE_STALE_SECONDS", "21600"))
WEATHER_FRIENDLY_FALLBACK = "天气数据暂未返回，当前先按常规出行条件生成路线；出发前建议再次确认天气。"

EXTERNAL_CACHE_TTLS = {
    "weather": int(os.environ.get("WEATHER_CACHE_TTL_SECONDS", "1800")),
    "map_route": int(os.environ.get("MAP_ROUTE_CACHE_TTL_SECONDS", "1800")),
    "map_search": int(os.environ.get("MAP_SEARCH_CACHE_TTL_SECONDS", "1800")),
    "meituan": int(os.environ.get("MEITUAN_SEARCH_CACHE_TTL_SECONDS", "600")),
    "rag": int(os.environ.get("RAG_QUERY_CACHE_TTL_SECONDS", "1800")),
}
EXTERNAL_CIRCUIT_THRESHOLD = int(os.environ.get("EXTERNAL_CIRCUIT_THRESHOLD", "3"))
EXTERNAL_CIRCUIT_TTL_SECONDS = int(os.environ.get("EXTERNAL_CIRCUIT_TTL_SECONDS", "300"))
EXTERNAL_CACHE = {}
EXTERNAL_CIRCUITS = {}
EXTERNAL_GUARD_LOCK = threading.Lock()
FRIENDLY_BACKUP_MESSAGE = "数据暂未返回，已启用备用方案。"
MAP_ROUTE_FRIENDLY_FALLBACK = "地图路线暂未返回，已保留路线节点，可稍后重新打开地图。"
MEITUAN_REAL_FRIENDLY_FALLBACK = "美团真实资源暂未返回，当前可使用 Mock 演示数据完成下单流程。"

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

def _friendly_external_error(text: str = "") -> str:
    s = str(text or FRIENDLY_BACKUP_MESSAGE)
    if re.search(r"API|429|timeout|timed out|限流|Key|WebService|raw response|raw_text|高德错误|AMap|AMAP|接口|报错", s, re.I):
        return FRIENDLY_BACKUP_MESSAGE
    return s or FRIENDLY_BACKUP_MESSAGE

def _external_cache_key(api: str, payload) -> str:
    raw = json.dumps(payload, ensure_ascii=False, sort_keys=True, default=str)
    return f"{api}:{hashlib.sha256(raw.encode('utf-8')).hexdigest()}"

def _external_cache_get(api: str, payload, ttl: int = None) -> Optional[dict]:
    key = _external_cache_key(api, payload)
    max_age = ttl if ttl is not None else EXTERNAL_CACHE_TTLS.get(api, 1800)
    now = time.time()
    with EXTERNAL_GUARD_LOCK:
        item = EXTERNAL_CACHE.get(key)
    if not item or now - item.get("ts", 0) > max_age:
        return None
    data = json.loads(json.dumps(item.get("data") or {}, ensure_ascii=False))
    data["cached"] = True
    return data

def _external_cache_set(api: str, payload, data: dict) -> None:
    key = _external_cache_key(api, payload)
    with EXTERNAL_GUARD_LOCK:
        EXTERNAL_CACHE[key] = {"ts": time.time(), "data": json.loads(json.dumps(data or {}, ensure_ascii=False))}

def _external_circuit_open(api: str) -> bool:
    with EXTERNAL_GUARD_LOCK:
        state = EXTERNAL_CIRCUITS.get(api) or {}
        return time.time() < float(state.get("open_until") or 0)

def _external_circuit_record(api: str, success: bool, reason: str = "") -> None:
    with EXTERNAL_GUARD_LOCK:
        state = EXTERNAL_CIRCUITS.setdefault(api, {"failures": 0, "open_until": 0.0, "reason": ""})
        if success:
            state.update({"failures": 0, "open_until": 0.0, "reason": ""})
            return
        failures = int(state.get("failures") or 0) + 1
        state["failures"] = failures
        state["reason"] = _safe_error_text(reason)[:160]
        if failures >= EXTERNAL_CIRCUIT_THRESHOLD:
            state["open_until"] = time.time() + EXTERNAL_CIRCUIT_TTL_SECONDS
            print(f"[EXTERNAL_CIRCUIT_OPEN] api={api} seconds={EXTERNAL_CIRCUIT_TTL_SECONDS} reason={state['reason']}", flush=True)

def _external_fallback_result(api: str, message: str = FRIENDLY_BACKUP_MESSAGE, cached_payload=None) -> dict:
    cached = _external_cache_get(api, cached_payload, ttl=EXTERNAL_CACHE_TTLS.get(api, 1800)) if cached_payload is not None else None
    if cached:
        cached["stale"] = True
        cached.setdefault("message", message)
        return cached
    return {"success": False, "friendly": True, "message": message, "error": message}

def _weather_cache_key(loc: dict) -> str:
    try:
        return f"coord:{round(float(loc.get('lat')), 3)}:{round(float(loc.get('lng')), 3)}"
    except Exception:
        return "city:" + _city_alias(str(loc.get("name") or "当前位置")).lower()

def _weather_cached(key: str, max_age: int) -> Optional[dict]:
    now = time.time()
    with WEATHER_CACHE_LOCK:
        item = WEATHER_CACHE.get(key)
    if not item or now - item.get("ts", 0) > max_age:
        return None
    data = json.loads(json.dumps(item.get("data") or {}, ensure_ascii=False))
    if now - item.get("ts", 0) > WEATHER_CACHE_TTL_SECONDS:
        data["cached"] = True
        data["stale"] = True
        data["message"] = "天气服务暂时繁忙，已显示最近一次可用天气。"
    else:
        data["cached"] = True
    return data

def _weather_store(key: str, data: dict) -> None:
    with WEATHER_CACHE_LOCK:
        WEATHER_CACHE[key] = {"ts": time.time(), "data": data}

def _weather_fallback_result(loc: dict, err=None) -> dict:
    key = _weather_cache_key(loc)
    cached = _weather_cached(key, WEATHER_CACHE_STALE_SECONDS)
    if cached:
        return cached
    print(f"[WEATHER_FALLBACK] {_safe_error_text(err)}")
    return {
        "success": False,
        "friendly": True,
        "city": loc.get("name") or "当前位置",
        "error": WEATHER_FRIENDLY_FALLBACK,
        "message": WEATHER_FRIENDLY_FALLBACK,
    }

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

def _safe_user_id(value: str = "") -> str:
    raw = str(value or "").strip()
    safe = re.sub(r"[^A-Za-z0-9_.:-]", "_", raw)[:80]
    return safe or "default_user"

def _request_user_id(payload: dict = None) -> str:
    payload = payload if isinstance(payload, dict) else {}
    return _safe_user_id(
        payload.get("user_id")
        or request.headers.get("X-User-ID")
        or request.args.get("user_id")
        or payload.get("session_user_id")
        or ""
    )

def _scoped_session_id(session_id: str = "default", user_id: str = "") -> str:
    return f"{_safe_user_id(user_id)}:{session_id or 'default'}"

def _init_history_db():
    with _history_conn() as conn:
        conn.execute("""
            CREATE TABLE IF NOT EXISTS chat_messages (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id TEXT NOT NULL DEFAULT 'default_user',
                session_id TEXT NOT NULL DEFAULT 'default',
                role TEXT NOT NULL,
                content TEXT NOT NULL,
                city TEXT DEFAULT '',
                persona TEXT DEFAULT '',
                lang TEXT DEFAULT 'zh',
                created_at INTEGER NOT NULL
            )
        """)
        existing_cols = {r["name"] for r in conn.execute("PRAGMA table_info(chat_messages)").fetchall()}
        for col, ddl in {
            "user_id": "ALTER TABLE chat_messages ADD COLUMN user_id TEXT NOT NULL DEFAULT 'default_user'",
            "message_type": "ALTER TABLE chat_messages ADD COLUMN message_type TEXT DEFAULT 'text'",
            "plan_json": "ALTER TABLE chat_messages ADD COLUMN plan_json TEXT",
            "order_json": "ALTER TABLE chat_messages ADD COLUMN order_json TEXT",
            "meta_json": "ALTER TABLE chat_messages ADD COLUMN meta_json TEXT",
        }.items():
            if col not in existing_cols:
                conn.execute(ddl)
        conn.execute("CREATE INDEX IF NOT EXISTS idx_chat_messages_created ON chat_messages(created_at DESC)")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_chat_messages_session ON chat_messages(session_id, created_at DESC)")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_chat_messages_user ON chat_messages(user_id, created_at DESC)")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_chat_messages_user_session ON chat_messages(user_id, session_id, created_at DESC)")
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

def _parse_history_json_content(content: str) -> dict:
    text = _clean_markdown(content or "")
    if not text or not text.lstrip().startswith("{"):
        return {}
    try:
        obj = json.loads(text)
    except Exception:
        return {}
    return obj if isinstance(obj, dict) else {}

def _history_summary_from_plan(plan: dict) -> str:
    if not isinstance(plan, dict):
        return "已生成行程方案"
    return str(plan.get("route_title") or plan.get("title") or plan.get("summary") or "已生成行程方案")[:120]

def _history_summary_from_restaurants(payload: dict) -> str:
    if not isinstance(payload, dict):
        return "餐厅推荐"
    restaurants = payload.get("restaurants") if isinstance(payload.get("restaurants"), list) else []
    first = restaurants[0].get("name") if restaurants and isinstance(restaurants[0], dict) else ""
    title = payload.get("title") or "餐厅推荐"
    city = payload.get("city") or payload.get("destination") or ""
    if first:
        return f"🍊 {city}{title}：{first}"[:120]
    return f"🍊 {city}{title}"[:120]

def _history_row_to_dict(row) -> dict:
    item = dict(row)
    msg_type = item.get("message_type") or "text"
    plan_json = item.get("plan_json")
    order_json = item.get("order_json")
    meta_json = item.get("meta_json")
    if plan_json:
        try:
            item["plan_json"] = json.loads(plan_json)
        except Exception:
            item["plan_json"] = None
    else:
        item["plan_json"] = None
    if order_json:
        try:
            item["order_json"] = json.loads(order_json)
        except Exception:
            item["order_json"] = None
    else:
        item["order_json"] = None
    if meta_json:
        try:
            item["meta_json"] = json.loads(meta_json)
        except Exception:
            item["meta_json"] = None
    else:
        item["meta_json"] = None
    legacy = _parse_history_json_content(item.get("content", ""))
    if msg_type == "text" and legacy.get("answer_type") == "trip_plan":
        item["message_type"] = "trip_plan"
        item["plan_json"] = legacy
        item["content"] = _history_summary_from_plan(legacy)
        print("[HISTORY_PARSE_LEGACY_JSON] trip_plan")
    elif msg_type == "text" and legacy.get("reply_type") == "restaurant_recommendations":
        item["message_type"] = "restaurant_recommendations"
        item["meta_json"] = legacy
        item["content"] = _history_summary_from_restaurants(legacy)
        print("[HISTORY_PARSE_LEGACY_JSON] restaurant_recommendations")
    else:
        item["message_type"] = msg_type
    return item

def _save_history_message(role: str, content: str, city: str = "",
                          persona: str = "", session_id: str = "default",
                          lang: str = "zh", message_type: str = "text",
                          plan_json=None, order_json=None, meta_json=None,
                          user_id: str = "default_user") -> dict:
    text = _clean_markdown(content)
    parsed_plan = plan_json if isinstance(plan_json, dict) else None
    parsed_meta = meta_json if isinstance(meta_json, dict) else None
    if not parsed_plan:
        legacy = _parse_history_json_content(text)
        if legacy.get("answer_type") == "trip_plan":
            parsed_plan = legacy
            message_type = "trip_plan"
            text = _history_summary_from_plan(parsed_plan)
        elif legacy.get("reply_type") == "restaurant_recommendations":
            parsed_meta = legacy
            message_type = "restaurant_recommendations"
            text = _history_summary_from_restaurants(parsed_meta)
    if parsed_plan:
        message_type = "trip_plan"
        text = _history_summary_from_plan(parsed_plan)
    if isinstance(parsed_meta, dict) and parsed_meta.get("reply_type") == "restaurant_recommendations":
        message_type = "restaurant_recommendations"
        text = _history_summary_from_restaurants(parsed_meta)
    if not text:
        return {}
    now = int(time.time())
    plan_text = json.dumps(parsed_plan, ensure_ascii=False) if parsed_plan else (plan_json if isinstance(plan_json, str) else None)
    order_text = json.dumps(order_json, ensure_ascii=False) if isinstance(order_json, dict) else (order_json if isinstance(order_json, str) else None)
    meta_text = json.dumps(parsed_meta, ensure_ascii=False) if isinstance(parsed_meta, dict) else (meta_json if isinstance(meta_json, str) else None)
    user_id = _safe_user_id(user_id)
    with _history_conn() as conn:
        cur = conn.execute(
            """INSERT INTO chat_messages(user_id, session_id, role, message_type, content, plan_json, order_json, meta_json, city, persona, lang, created_at)
               VALUES (?,?,?,?,?,?,?,?,?,?,?,?)""",
            (user_id, session_id or "default", role or "assistant", message_type or "text", text[:8000], plan_text, order_text, meta_text, city or "", persona or "", lang or "zh", now),
        )
        print(f"[HISTORY_SAVE] user_id={user_id} message_type={message_type or 'text'}")
        return {"id": cur.lastrowid, "created_at": now}

def _search_history(q: str = "", limit: int = 30, user_id: str = "default_user") -> list:
    q = (q or "").strip()
    limit = max(1, min(int(limit or 30), 80))
    user_id = _safe_user_id(user_id)
    with _history_conn() as conn:
        if q:
            rows = []
            try:
                rows = conn.execute("""
                    SELECT m.* FROM chat_messages_fts f
                    JOIN chat_messages m ON m.id = f.rowid
                    WHERE chat_messages_fts MATCH ? AND m.user_id = ?
                    ORDER BY rank
                    LIMIT ?
                """, (q, user_id, limit)).fetchall()
            except Exception:
                rows = []
            if not rows:
                like = f"%{q}%"
                rows = conn.execute("""
                    SELECT * FROM chat_messages
                    WHERE user_id = ? AND (content LIKE ? OR city LIKE ? OR persona LIKE ?)
                    ORDER BY created_at DESC
                    LIMIT ?
                """, (user_id, like, like, like, limit)).fetchall()
        else:
            rows = conn.execute("SELECT * FROM chat_messages WHERE user_id = ? ORDER BY created_at DESC LIMIT ?", (user_id, limit)).fetchall()
    items = [_history_row_to_dict(r) for r in rows]
    print(f"[HISTORY_LOAD] user_id={user_id} count={len(items)}")
    return items

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
    payload = {"city": _city_alias(city or "")}
    cached = _external_cache_get("weather", {"geocode": payload})
    if cached:
        return cached.get("loc")
    if _external_circuit_open("weather"):
        return None
    try:
        r=requests.get(OM_GEO_URL,params={"name":city,"count":1,"language":"zh","format":"json"},timeout=REQUEST_TIMEOUT)
        r.raise_for_status()
        res=r.json().get("results")
        if res:
            loc=res[0]
            out = {"lat":loc["latitude"],"lng":loc["longitude"],"name":loc.get("name",city),"country":loc.get("country","")}
            _external_cache_set("weather", {"geocode": payload}, {"success": True, "loc": out})
            _external_circuit_record("weather", True)
            return out
        _external_circuit_record("weather", False, "empty_geocode")
    except Exception as e:
        _external_circuit_record("weather", False, _safe_error_text(e))
        print(f"[om_geo]{_safe_error_text(e)}")
    return None

def geocode_baidu(address: str, city: str = "") -> Optional[dict]:
    payload = {"address": address or "", "city": city or ""}
    cached = _external_cache_get("map_search", {"baidu_geocode": payload})
    if cached:
        return cached.get("loc")
    if _external_circuit_open("baidu_map"):
        return None
    try:
        r=requests.get(BAIDU_GEOCODE_URL,params={"address":address,"city":city,"output":"json","ak":BAIDU_AK},timeout=REQUEST_TIMEOUT)
        d=r.json()
        if d.get("status")==0:
            loc=d["result"]["location"]
            out = {"lat":loc["lat"],"lng":loc["lng"]}
            _external_cache_set("map_search", {"baidu_geocode": payload}, {"success": True, "loc": out})
            _external_circuit_record("baidu_map", True)
            return out
        _external_circuit_record("baidu_map", False, d.get("message", "baidu_geocode_failed"))
    except Exception as e:
        _external_circuit_record("baidu_map", False, _safe_error_text(e))
        print(f"[baidu_geo]{_safe_error_text(e)}")
    return None

def geocode_amap(address: str, city: str = "") -> Optional[dict]:
    """高德地理编码：优先服务路线/POI 地图数据，缺 Key 时静默回退。"""
    payload = {"address": address or "", "city": city or ""}
    cached = _external_cache_get("map_search", {"amap_geocode": payload})
    if cached:
        return cached.get("loc")
    if not AMAP_WEBSERVICE_KEY or not address:
        reason = "missing_key" if not AMAP_WEBSERVICE_KEY else "missing_address"
        _remember_amap_error(reason)
        _log_amap("AMAP_GEOCODE", False, 0, city=city, address=address or "", reason=reason)
        return geocode_baidu(address, city) if address else None
    if _amap_circuit_open():
        _log_amap("AMAP_GEOCODE", False, 0, city=city, address=address or "", reason="circuit_open")
        return geocode_baidu(address, city)
    t0 = time.perf_counter()
    try:
        r = requests.get(AMAP_GEOCODE_URL, params={
            "address": address,
            "city": city or "",
            "output": "JSON",
            "key": AMAP_WEBSERVICE_KEY,
        }, timeout=REQUEST_TIMEOUT)
        elapsed = round((time.perf_counter() - t0) * 1000)
        d = r.json()
        geos = d.get("geocodes") or []
        if d.get("status") == "1" and geos:
            loc = (geos[0].get("location") or "").split(",")
            if len(loc) == 2:
                _log_amap("AMAP_GEOCODE", True, elapsed, city=city, address=address)
                _clear_amap_error()
                out = {
                    "lng": float(loc[0]),
                    "lat": float(loc[1]),
                    "name": geos[0].get("formatted_address") or address,
                    "source": "amap_geocode",
                    **_amap_meta(True, elapsed),
                }
                _external_cache_set("map_search", {"amap_geocode": payload}, {"success": True, "loc": out})
                return out
        reason = d.get("info", "no_geocode")
        _remember_amap_error(reason)
        _log_amap("AMAP_GEOCODE", False, elapsed, city=city, address=address, reason=reason)
    except Exception as e:
        elapsed = round((time.perf_counter() - t0) * 1000)
        _log_amap("AMAP_GEOCODE", False, elapsed, city=city, address=address, reason=_safe_error_text(e))
        _external_circuit_record("map_search", False, _safe_error_text(e))
    return geocode_baidu(address, city)

def search_amap_place(query: str, city: str = "", limit: int = 5,
                      location: str = "", radius: int = 3000) -> list:
    """高德 POI 搜索：用于高德优先的酒店/美食/景点补充。"""
    print("🟢 [AMAP_POI] city=", city, "keyword=", query)
    payload = {"query": query or "", "city": city or "", "limit": int(limit or 5), "location": location or "", "radius": int(radius or 3000)}
    cached = _external_cache_get("map_search", {"amap_place": payload})
    if cached:
        return cached.get("items") or []
    if not AMAP_WEBSERVICE_KEY or not query:
        reason = "missing_key" if not AMAP_WEBSERVICE_KEY else "missing_query"
        _remember_amap_error(reason)
        _log_amap("AMAP_POI", False, 0, city=city, query=query or "", reason=reason)
        return _baidu_places_as_map_items(search_baidu_place(query, city, limit), query, city)
    if _amap_circuit_open():
        _log_amap("AMAP_POI", False, 0, city=city, query=query or "", reason="circuit_open")
        return _baidu_places_as_map_items(search_baidu_place(query, city, limit), query, city)
    t0 = time.perf_counter()
    try:
        params = {
            "key": AMAP_WEBSERVICE_KEY,
            "keywords": query,
            "city": city or "",
            "output": "JSON",
            "offset": min(max(int(limit or 5), 1), 25),
            "extensions": "all",
        }
        # 禁止跨城市：限定只返回指定城市的 POI，避免 amap 在本地无匹配时回退到全国结果(曾把封开搜成重庆)
        if city and not location:
            params["citylimit"] = "true"
        if location:
            params["location"] = location
            params["radius"] = int(radius or 3000)
            params["sortrule"] = "distance"
        r = requests.get(AMAP_PLACE_TEXT_URL, params=params, timeout=REQUEST_TIMEOUT)
        elapsed = round((time.perf_counter() - t0) * 1000)
        d = r.json()
        if d.get("status") != "1":
            reason = d.get("info", "amap_poi_failed")
            _remember_amap_error(reason)
            _log_amap("AMAP_POI", False, elapsed, city=city, query=query, reason=reason)
            _external_circuit_record("map_search", False, reason)
            return _baidu_places_as_map_items(search_baidu_place(query, city, limit), query, city)
        out = []
        for p in (d.get("pois") or [])[:limit]:
            loc = str(p.get("location") or "")
            lng, lat = ("", "")
            if "," in loc:
                lng, lat = loc.split(",", 1)
            biz = p.get("biz_ext") or {}
            out.append({
                "name": p.get("name", ""),
                "address": p.get("address", ""),
                "rating": biz.get("rating", ""),
                "cost": biz.get("cost", ""),
                "distance": p.get("distance", ""),
                "type": p.get("type", ""),
                "tel": p.get("tel", ""),
                "location": loc,
                "lng": float(lng) if lng else None,
                "lat": float(lat) if lat else None,
                "photo_url": ((p.get("photos") or [{}])[0].get("url", "") if isinstance(p.get("photos"), list) else ""),
                "source": "高德地图",
                "query_city": city or "",
                "data_source": "amap",
                "tool_name": "amap-lbs-skill",
                "success": True,
                "elapsed_ms": elapsed,
                "data_level": "B_REAL_MAP_POI",
                "is_real_poi": True,
                "can_order": False,
                "advantage": "地图参考，需二次确认营业状态后再加入行程。",
            })
        _log_amap("AMAP_POI", bool(out), elapsed, city=city, query=query, count=len(out))
        if out:
            _clear_amap_error()
            _external_cache_set("map_search", {"amap_place": payload}, {"success": True, "items": out})
            _external_circuit_record("map_search", True)
        return out
    except Exception as e:
        elapsed = round((time.perf_counter() - t0) * 1000)
        _log_amap("AMAP_POI", False, elapsed, city=city, query=query, reason=_safe_error_text(e))
        _external_circuit_record("map_search", False, _safe_error_text(e))
    return _baidu_places_as_map_items(search_baidu_place(query, city, limit), query, city)

def search_amap_around_facility(lat: float, lng: float, types: str,
                                radius: int = 2000, limit: int = 8) -> list:
    """高德周边类型搜索：把商场/地铁站/加油站/公园/快餐等"内部通常有卫生间"的场所
    当成派生厕所点返回。types 为高德类型码，可用 | 分隔多个。"""
    if lat is None or lng is None or not types:
        return []
    if not AMAP_WEBSERVICE_KEY:
        _remember_amap_error("missing_key")
        return []
    if _amap_circuit_open():
        _log_amap("AMAP_POI", False, 0, query=types, reason="circuit_open")
        return []
    t0 = time.perf_counter()
    try:
        params = {
            "key": AMAP_WEBSERVICE_KEY,
            "location": f"{float(lng)},{float(lat)}",
            "types": types,
            "radius": int(radius or 2000),
            "sortrule": "distance",
            "offset": min(max(int(limit or 8), 1), 25),
            "page": 1,
            "extensions": "base",
            "output": "JSON",
        }
        r = requests.get(AMAP_PLACE_AROUND_URL, params=params, timeout=REQUEST_TIMEOUT)
        elapsed = round((time.perf_counter() - t0) * 1000)
        d = r.json()
        if d.get("status") != "1":
            reason = d.get("info", "amap_around_failed")
            _remember_amap_error(reason)
            _log_amap("AMAP_POI", False, elapsed, query=types, reason=reason)
            return []
        out = []
        for p in (d.get("pois") or [])[:limit]:
            loc = str(p.get("location") or "")
            plng, plat = ("", "")
            if "," in loc:
                plng, plat = loc.split(",", 1)
            # 用该 POI 自身的高德类型码判定它代表哪类"可借厕所"场所；
            # typecode 匹配不到时，退回到本次查询第一个类型码对应的标签。
            type_code = str(p.get("typecode") or "")
            label = ""
            for code, name in AMAP_TOILET_SUPPORT_TYPES.items():
                if type_code.startswith(code[:4]):
                    label = name
                    break
            if not label:
                first_code = str(types).split("|", 1)[0].strip()
                label = AMAP_TOILET_SUPPORT_TYPES.get(first_code, "可尝试地点")
            dist = p.get("distance") or ""
            out.append({
                "name": p.get("name", ""),
                "address": p.get("address", "") or "",
                "rating": "",
                "cost": "",
                "distance": dist,
                "type": label,
                "tel": p.get("tel", "") or "",
                "location": loc,
                "lng": float(plng) if plng else None,
                "lat": float(plat) if plat else None,
                "source": "高德地图",
                "query_city": "",
                "data_source": "amap",
                "tool_name": "amap-toilet-support-around",
                "success": True,
                "elapsed_ms": elapsed,
                "data_level": "B_REAL_TOILET_SUPPORT",
                "is_real_poi": True,
                "can_order": False,
                "facility_query": label,
                "advantage": "进入后找卫生间，开放状态需现场确认。",
            })
        out.sort(key=lambda x: int(float(x.get("distance") or 999999)) if str(x.get("distance") or "").strip() else 999999)
        _log_amap("AMAP_POI", bool(out), elapsed, query=types, count=len(out))
        if out:
            _clear_amap_error()
        return out[:limit]
    except Exception as e:
        elapsed = round((time.perf_counter() - t0) * 1000)
        _log_amap("AMAP_POI", False, elapsed, query=types, reason=_safe_error_text(e))
    return []

def search_public_toilets_osm(lat: float, lng: float, radius: int = 1000, limit: int = 8) -> list:
    """Nearest real public toilets from OpenStreetMap. User-facing copy stays provider-neutral."""
    if lat is None or lng is None:
        return []
    url = "https://overpass-api.de/api/interpreter"
    query = f"""
    [out:json][timeout:4];
    (
      node(around:{int(radius)},{float(lat)},{float(lng)})["amenity"="toilets"];
      way(around:{int(radius)},{float(lat)},{float(lng)})["amenity"="toilets"];
      relation(around:{int(radius)},{float(lat)},{float(lng)})["amenity"="toilets"];
    );
    out center tags {max(1, min(int(limit or 8), 20))};
    """
    t0 = time.perf_counter()
    try:
        r = _HTTP_SESSION.post(url, data={"data": query}, timeout=5)
        elapsed = round((time.perf_counter() - t0) * 1000)
        d = r.json()
        out = []
        for el in d.get("elements") or []:
            tags = el.get("tags") or {}
            plat = el.get("lat") or (el.get("center") or {}).get("lat")
            plng = el.get("lon") or (el.get("center") or {}).get("lon")
            if plat is None or plng is None:
                continue
            dist = round(_haversine(float(lat), float(lng), float(plat), float(plng)) * 1000)
            addr = " ".join([
                str(tags.get("addr:housenumber") or ""),
                str(tags.get("addr:street") or ""),
                str(tags.get("addr:postcode") or ""),
            ]).strip()
            detail_bits = []
            if tags.get("access"):
                detail_bits.append(f"开放性：{tags.get('access')}")
            if tags.get("fee"):
                detail_bits.append(f"收费：{tags.get('fee')}")
            if tags.get("wheelchair"):
                detail_bits.append(f"无障碍：{tags.get('wheelchair')}")
            if tags.get("opening_hours"):
                detail_bits.append(f"时间：{tags.get('opening_hours')}")
            out.append({
                "name": tags.get("name") or tags.get("operator") or "公共卫生间",
                "address": addr or tags.get("description") or "",
                "rating": "",
                "cost": "",
                "distance": dist,
                "type": "公共卫生间",
                "tel": "",
                "location": f"{float(plng)},{float(plat)}",
                "lng": float(plng),
                "lat": float(plat),
                "source": "地图参考",
                "query_city": "",
                "data_source": "osm",
                "tool_name": "public-toilet-search",
                "success": True,
                "elapsed_ms": elapsed,
                "data_level": "B_REAL_PUBLIC_TOILET",
                "is_real_poi": True,
                "can_order": False,
                "facility_query": "公共卫生间",
                "advantage": "真实卫生间位置，开放状态需现场二次确认。",
                "note": "；".join(detail_bits),
            })
        out.sort(key=lambda x: int(x.get("distance") or 999999))
        _record_tool_call("public_toilet_search", "success" if out else "empty", elapsed,
                          radius=radius, count=len(out))
        return out[:limit]
    except Exception as e:
        _record_tool_call("public_toilet_search", "error",
                          round((time.perf_counter() - t0) * 1000),
                          radius=radius, error=_safe_error_text(e)[:120])
        return []

def search_nearby_toilet_support_osm(lat: float, lng: float, radius: int = 3000,
                                     limit: int = 8, stage: str = "") -> list:
    """Find real nearby places that commonly have toilets: malls, stations, parks, cafes, fuel."""
    if lat is None or lng is None:
        return []
    url = "https://overpass-api.de/api/interpreter"
    query = f"""
    [out:json][timeout:4];
    (
      node(around:{int(radius)},{float(lat)},{float(lng)})["amenity"~"school|university|college|fuel|restaurant|cafe|fast_food|food_court|library|community_centre"];
      way(around:{int(radius)},{float(lat)},{float(lng)})["amenity"~"school|university|college|fuel|restaurant|cafe|fast_food|food_court|library|community_centre"];
      relation(around:{int(radius)},{float(lat)},{float(lng)})["amenity"~"school|university|college|fuel|restaurant|cafe|fast_food|food_court|library|community_centre"];
      node(around:{int(radius)},{float(lat)},{float(lng)})["shop"="mall"];
      way(around:{int(radius)},{float(lat)},{float(lng)})["shop"="mall"];
      relation(around:{int(radius)},{float(lat)},{float(lng)})["shop"="mall"];
      node(around:{int(radius)},{float(lat)},{float(lng)})["shop"="convenience"];
      way(around:{int(radius)},{float(lat)},{float(lng)})["shop"="convenience"];
      relation(around:{int(radius)},{float(lat)},{float(lng)})["shop"="convenience"];
      node(around:{int(radius)},{float(lat)},{float(lng)})["railway"="station"];
      way(around:{int(radius)},{float(lat)},{float(lng)})["railway"="station"];
      node(around:{int(radius)},{float(lat)},{float(lng)})["public_transport"="station"];
      way(around:{int(radius)},{float(lat)},{float(lng)})["public_transport"="station"];
      node(around:{int(radius)},{float(lat)},{float(lng)})["leisure"="park"];
      way(around:{int(radius)},{float(lat)},{float(lng)})["leisure"="park"];
      relation(around:{int(radius)},{float(lat)},{float(lng)})["leisure"="park"];
      node(around:{int(radius)},{float(lat)},{float(lng)})["tourism"~"information|attraction"];
      way(around:{int(radius)},{float(lat)},{float(lng)})["tourism"~"information|attraction"];
      relation(around:{int(radius)},{float(lat)},{float(lng)})["tourism"~"information|attraction"];
    );
    out center tags {max(1, min(int(limit or 8), 20))};
    """
    t0 = time.perf_counter()
    label_map = {
        "school": "学校",
        "university": "高校",
        "college": "高校",
        "fuel": "加油站",
        "restaurant": "餐厅",
        "cafe": "咖啡店",
        "fast_food": "餐饮中心",
        "food_court": "餐饮中心",
        "library": "图书馆",
        "community_centre": "社区中心",
        "mall": "商场",
        "convenience": "便利店",
        "station": "地铁站/车站",
        "park": "公园",
        "information": "游客中心",
        "attraction": "景点服务区",
    }
    stage_labels = {
        "mall": {"商场"},
        "station": {"地铁站/车站"},
        "likely": {"公园", "加油站", "咖啡店", "餐厅", "餐饮中心", "便利店", "图书馆", "社区中心", "游客中心", "景点服务区", "学校", "高校"},
        "core_backup": {"商场", "地铁站/车站", "公园", "加油站"},
        "all": set(),
    }
    try:
        r = _HTTP_SESSION.post(url, data={"data": query}, timeout=5)
        elapsed = round((time.perf_counter() - t0) * 1000)
        d = r.json()
        out = []
        for el in d.get("elements") or []:
            tags = el.get("tags") or {}
            plat = el.get("lat") or (el.get("center") or {}).get("lat")
            plng = el.get("lon") or (el.get("center") or {}).get("lon")
            if plat is None or plng is None:
                continue
            raw_kind = (
                tags.get("amenity") or tags.get("shop") or tags.get("railway")
                or tags.get("public_transport") or tags.get("leisure") or tags.get("tourism") or "地点"
            )
            kind = label_map.get(str(raw_kind), str(raw_kind))
            allowed = stage_labels.get(stage or "all", set())
            if allowed and kind not in allowed:
                continue
            name = tags.get("name") or tags.get("operator") or kind
            dist = round(_haversine(float(lat), float(lng), float(plat), float(plng)) * 1000)
            out.append({
                "name": name,
                "address": tags.get("addr:full") or tags.get("addr:street") or "",
                "rating": "",
                "cost": "",
                "distance": dist,
                "type": kind,
                "tel": "",
                "location": f"{float(plng)},{float(plat)}",
                "lng": float(plng),
                "lat": float(plat),
                "source": "地图参考",
                "query_city": "",
                "data_source": "osm",
                "tool_name": "nearby-toilet-support-search",
                "success": True,
                "elapsed_ms": elapsed,
                "data_level": "B_REAL_TOILET_SUPPORT",
                "is_real_poi": True,
                "can_order": False,
                "facility_query": kind,
                "advantage": "可借用卫生间地点，开放状态需现场确认。",
            })
        out.sort(key=lambda x: int(x.get("distance") or 999999))
        _record_tool_call("toilet_support_search", "success" if out else "empty", elapsed,
                          radius=radius, count=len(out))
        return out[:limit]
    except Exception as e:
        _record_tool_call("toilet_support_search", "error",
                          round((time.perf_counter() - t0) * 1000),
                          radius=radius, error=_safe_error_text(e)[:120])
        return []

def search_nearby_toilet_nominatim(lat: float, lng: float, queries: list,
                                   radius: int = 3000, limit: int = 8,
                                   stage: str = "") -> list:
    """Fallback nearby search from OSM Nominatim, used when Overpass or map services return empty."""
    if lat is None or lng is None:
        return []
    try:
        lat_f, lng_f = float(lat), float(lng)
    except Exception:
        return []
    radius = max(300, int(radius or 3000))
    lat_delta = radius / 111320.0
    lng_delta = radius / max(40000.0, (111320.0 * max(0.25, math.cos(math.radians(lat_f)))))
    west, east = lng_f - lng_delta, lng_f + lng_delta
    north, south = lat_f + lat_delta, lat_f - lat_delta
    url = "https://nominatim.openstreetmap.org/search"
    labels = {
        "explicit_toilet": "公共卫生间",
        "mall": "商场",
        "station": "地铁站",
        "likely": "",
        "core_backup": "",
    }
    def _label_for_query(q: str) -> str:
        ql = str(q or "").lower()
        if re.search(r"toilet|restroom|washroom|bathroom|厕所|卫生间|公厕|洗手间", ql):
            return "公共卫生间"
        if re.search(r"mall|shopping|商场|购物", ql):
            return "商场"
        if re.search(r"mrt|metro|subway|station|地铁|车站", ql):
            return "地铁站"
        if re.search(r"petrol|gas|fuel|加油", ql):
            return "加油站"
        if re.search(r"park|公园", ql):
            return "公园"
        if re.search(r"library|图书馆", ql):
            return "图书馆"
        if re.search(r"community|社区", ql):
            return "社区中心"
        if re.search(r"food court|hawker|餐饮", ql):
            return "餐饮中心"
        if re.search(r"cafe|coffee|咖啡", ql):
            return "咖啡店"
        if re.search(r"convenience|便利", ql):
            return "便利店"
        if re.search(r"tourist|游客", ql):
            return "游客中心"
        return labels.get(stage) or "可尝试地点"
    def _looks_right(row: dict, label: str) -> bool:
        blob = " ".join(str(row.get(k) or "") for k in ("name", "display_name", "category", "type", "addresstype")).lower()
        if label == "公共卫生间":
            return bool(re.search(r"toilet|restroom|washroom|bathroom|toilets|卫生间|厕所", blob))
        if label == "商场":
            return bool(re.search(r"mall|shopping centre|shopping center|商场|购物", blob))
        if label == "地铁站":
            return bool(re.search(r"mrt|metro|subway|station|地铁|车站", blob))
        if label == "加油站":
            return bool(re.search(r"fuel|petrol|gas station|加油", blob))
        if label == "公园":
            return bool(re.search(r"park|公园", blob))
        return True
    t0 = time.perf_counter()
    out = []
    try:
        for q in (queries or [])[:8]:
            label = _label_for_query(q)
            params = {
                "format": "jsonv2",
                "q": q,
                "bounded": 1,
                "viewbox": f"{west},{north},{east},{south}",
                "limit": max(1, min(int(limit or 8), 10)),
            }
            r = _HTTP_SESSION.get(url, params=params, timeout=4, headers={
                "User-Agent": "madao-orange-hackathon/1.0"
            })
            if not r.ok:
                continue
            for row in r.json() or []:
                plat = _coerce_float(row.get("lat"))
                plng = _coerce_float(row.get("lon"))
                if plat is None or plng is None:
                    continue
                dist = round(_haversine(lat_f, lng_f, plat, plng) * 1000)
                if dist > radius * 1.35:
                    continue
                if not _looks_right(row, label):
                    continue
                display = str(row.get("display_name") or "")
                name = str(row.get("name") or "").strip()
                if not name:
                    name = "公共卫生间" if label == "公共卫生间" else (display.split(",")[0].strip() or label)
                out.append({
                    "name": name,
                    "address": display,
                    "rating": "",
                    "cost": "",
                    "distance": dist,
                    "type": label,
                    "tel": "",
                    "location": f"{plng},{plat}",
                    "lng": plng,
                    "lat": plat,
                    "source": "地图参考",
                    "query_city": "",
                    "data_source": "nominatim",
                    "tool_name": "nearby-toilet-fallback-search",
                    "success": True,
                    "elapsed_ms": round((time.perf_counter() - t0) * 1000),
                    "data_level": "B_REAL_TOILET_CANDIDATE",
                    "is_real_poi": True,
                    "can_order": False,
                    "facility_query": label,
                    "facility_stage": stage,
                    "advantage": "附近可尝试地点，开放状态需现场确认。",
                })
        out.sort(key=lambda x: int(x.get("distance") or 999999))
        _record_tool_call("toilet_nominatim_search", "success" if out else "empty",
                          round((time.perf_counter() - t0) * 1000),
                          radius=radius, stage=stage, count=len(out))
        return out[:limit]
    except Exception as e:
        _record_tool_call("toilet_nominatim_search", "error",
                          round((time.perf_counter() - t0) * 1000),
                          radius=radius, stage=stage, error=_safe_error_text(e)[:120])
        return []

def _amap_coord_text(value: str, city: str = "") -> str:
    s = str(value or "").strip()
    if re.match(r"^\s*-?\d+(?:\.\d+)?\s*,\s*-?\d+(?:\.\d+)?\s*$", s):
        return re.sub(r"\s+", "", s)
    loc = geocode_amap(s, city)
    if loc and loc.get("lng") and loc.get("lat"):
        return f"{loc['lng']},{loc['lat']}"
    return ""

def _coord_for_baidu(value: str, city: str = "") -> Optional[dict]:
    pair = _parse_lat_lng(value)
    if pair:
        return pair
    s = str(value or "").strip()
    m = re.match(r"^\s*(-?\d+(?:\.\d+)?)\s*,\s*(-?\d+(?:\.\d+)?)\s*$", s)
    if m:
        a, b = float(m.group(1)), float(m.group(2))
        if abs(a) > 90 and abs(b) <= 90:
            return {"lat": b, "lng": a}
        if abs(a) <= 90 and abs(b) <= 180:
            return {"lat": a, "lng": b}
    return geocode_baidu(value, city)

def _baidu_route_backup(origin: str, destination: str, mode: str = "walking", city: str = "") -> dict:
    mode_key = {"walk": "walking", "drive": "walking", "bus": "walking", "bicycle": "riding", "riding": "riding"}.get(mode, mode or "walking")
    payload = {"origin": origin or "", "destination": destination or "", "mode": mode_key, "city": city or ""}
    cached = _external_cache_get("map_route", {"baidu_route": payload})
    if cached:
        return cached
    if _external_circuit_open("baidu_map"):
        return {"success": False, "error": MAP_ROUTE_FRIENDLY_FALLBACK, "message": MAP_ROUTE_FRIENDLY_FALLBACK, "provider": "baidu"}
    oc = _coord_for_baidu(origin, city)
    dc = _coord_for_baidu(destination, city)
    if not oc or not dc:
        return {"success": False, "error": MAP_ROUTE_FRIENDLY_FALLBACK, "message": MAP_ROUTE_FRIENDLY_FALLBACK, "provider": "baidu"}
    url = BAIDU_RIDING_URL if mode_key == "riding" else BAIDU_WALKING_URL
    t0 = time.perf_counter()
    try:
        params = {
            "origin": f"{oc['lat']},{oc['lng']}",
            "destination": f"{dc['lat']},{dc['lng']}",
            "steps_info": 1,
            "ret_coordtype": "bd09ll",
            "ak": BAIDU_AK,
        }
        if mode_key == "riding":
            params.update({"riding_type": 0, "road_prefer": 0})
        r = requests.get(url, params=params, timeout=REQUEST_TIMEOUT)
        elapsed = round((time.perf_counter() - t0) * 1000)
        d = r.json()
        if d.get("status") != 0:
            _external_circuit_record("baidu_map", False, d.get("message", "baidu_route_failed"))
            return {"success": False, "error": MAP_ROUTE_FRIENDLY_FALLBACK, "message": MAP_ROUTE_FRIENDLY_FALLBACK, "provider": "baidu"}
        best = (d.get("result", {}).get("routes") or [{}])[0]
        raw_steps = best.get("steps", []) or []
        points = _extract_baidu_path_points(raw_steps) or [oc, dc]
        out = {
            "success": True,
            "provider": "baidu",
            "map_engine": "地图路线引擎",
            "mode": mode_key,
            "origin": f"{oc['lng']},{oc['lat']}",
            "destination": f"{dc['lng']},{dc['lat']}",
            "distance_m": int(best.get("distance", 0) or 0),
            "duration_sec": int(best.get("duration", 0) or 0),
            "steps": raw_steps[:12],
            "points": points,
            "elapsed_ms": elapsed,
            "message": "地图路线已生成",
        }
        _external_cache_set("map_route", {"baidu_route": payload}, out)
        _external_circuit_record("baidu_map", True)
        return out
    except Exception as e:
        _external_circuit_record("baidu_map", False, _safe_error_text(e))
        return {"success": False, "error": MAP_ROUTE_FRIENDLY_FALLBACK, "message": MAP_ROUTE_FRIENDLY_FALLBACK, "provider": "baidu"}

def route_amap(origin: str, destination: str, mode: str = "walking", city: str = "") -> dict:
    """高德 Web Service 路径规划，返回轻量结构；缺 Key 时让调用方回退。"""
    payload = {"origin": origin or "", "destination": destination or "", "mode": mode or "walking", "city": city or ""}
    cached = _external_cache_get("map_route", {"amap_route": payload})
    if cached:
        return cached
    if not AMAP_WEBSERVICE_KEY:
        _remember_amap_error("missing_key")
        _log_amap("AMAP_ROUTE", False, 0, city=city, mode=mode, reason="missing_key")
        return _baidu_route_backup(origin, destination, mode, city)
    if _amap_circuit_open():
        _log_amap("AMAP_ROUTE", False, 0, city=city, mode=mode, reason="circuit_open")
        return _baidu_route_backup(origin, destination, mode, city)
    t0 = time.perf_counter()
    mode_key = {"walk": "walking", "drive": "driving", "bus": "transit", "bicycle": "riding"}.get(mode, mode)
    url = AMAP_ROUTE_URLS.get(mode_key, AMAP_ROUTE_URLS["walking"])
    o = _amap_coord_text(origin, city)
    d = _amap_coord_text(destination, city)
    if not o or not d:
        elapsed = round((time.perf_counter() - t0) * 1000)
        _log_amap("AMAP_ROUTE", False, elapsed, city=city, mode=mode_key, origin=origin, destination=destination, reason="coord_parse_failed")
        return _baidu_route_backup(origin, destination, mode, city)
    try:
        params = {"key": AMAP_WEBSERVICE_KEY, "origin": o, "destination": d, "output": "JSON"}
        if mode_key == "transit":
            params["city"] = city or ""
        r = requests.get(url, params=params, timeout=REQUEST_TIMEOUT)
        elapsed = round((time.perf_counter() - t0) * 1000)
        data = r.json()
        if data.get("status") != "1":
            reason = data.get("info", "route_failed")
            msg = _remember_amap_error(reason)
            _log_amap("AMAP_ROUTE", False, elapsed, city=city, mode=mode_key, origin=origin, destination=destination, reason=reason)
            _external_circuit_record("map_route", False, reason)
            return _baidu_route_backup(origin, destination, mode, city)
        route = data.get("route") or {}
        paths = route.get("paths") or route.get("transits") or []
        best = paths[0] if paths else {}
        route_points = _extract_amap_path_points(best.get("steps") or best.get("segments") or [])
        print("🟢 [AMAP_ROUTE] route_points=", route_points)
        _log_amap("AMAP_ROUTE", True, elapsed, city=city, mode=mode_key, origin=origin, destination=destination)
        _clear_amap_error()
        out = {
            "success": True,
            "provider": "gaode",
            **_amap_meta(True, elapsed),
            "mode": mode_key,
            "origin": o,
            "destination": d,
            "distance_m": int(float(best.get("distance") or 0)) if best else 0,
            "duration_sec": int(float(best.get("duration") or 0)) if best and best.get("duration") else 0,
            "steps": best.get("steps") or best.get("segments") or [],
            "points": route_points,
            "raw": data,
        }
        _external_cache_set("map_route", {"amap_route": payload}, out)
        _external_circuit_record("map_route", True)
        return out
    except Exception as e:
        elapsed = round((time.perf_counter() - t0) * 1000)
        _log_amap("AMAP_ROUTE", False, elapsed, city=city, mode=mode_key, origin=origin, destination=destination, reason=_safe_error_text(e))
        _external_circuit_record("map_route", False, _safe_error_text(e))
        return _baidu_route_backup(origin, destination, mode, city)

def search_baidu_place(query: str, city: str = "", limit: int = 3) -> list:
    """百度地点检索：用于周末 Agent 的真实基础 POI 坐标校准。"""
    payload = {"query": query or "", "city": city or "", "limit": int(limit or 3)}
    cached = _external_cache_get("map_search", {"baidu_place": payload})
    if cached:
        return cached.get("items") or []
    if _external_circuit_open("baidu_map"):
        return []
    try:
        r = requests.get(BAIDU_PLACE_URL, params={
            "query": query, "region": city or "全国", "output": "json",
            "scope": 2, "page_size": min(limit, 10), "ak": BAIDU_AK
        }, timeout=REQUEST_TIMEOUT)
        d = r.json()
        if d.get("status") == 0:
            items = d.get("results", [])[:limit]
            _external_cache_set("map_search", {"baidu_place": payload}, {"success": True, "items": items})
            _external_circuit_record("baidu_map", True)
            return items
        _external_circuit_record("baidu_map", False, d.get("message", "baidu_place_failed"))
    except Exception as e:
        _external_circuit_record("baidu_map", False, _safe_error_text(e))
        print(f"[baidu_place]{_safe_error_text(e)}")
    return []

def _baidu_places_as_map_items(rows: list, query: str = "", city: str = "") -> list:
    out = []
    for p in (rows or []):
        loc = p.get("location") or {}
        lat = _coerce_float(loc.get("lat") if isinstance(loc, dict) else None)
        lng = _coerce_float(loc.get("lng") if isinstance(loc, dict) else None)
        item = {
            "name": p.get("name", ""),
            "address": p.get("address", ""),
            "rating": "",
            "cost": "",
            "distance": p.get("distance", ""),
            "type": p.get("detail_info", {}).get("tag", "") if isinstance(p.get("detail_info"), dict) else "",
            "tel": p.get("telephone", ""),
            "location": f"{lng},{lat}" if lat is not None and lng is not None else "",
            "lng": lng,
            "lat": lat,
            "photo_url": "",
            "source": "地图参考",
            "query_city": city or "",
            "data_source": "baidu",
            "tool_name": "baidu-map-backup",
            "success": True,
            "elapsed_ms": 0,
            "data_level": "B_REAL_MAP_POI",
            "is_real_poi": True,
            "can_order": False,
            "advantage": "地图参考，需二次确认营业状态后再加入行程。",
        }
        if item["name"]:
            out.append(item)
    if out:
        _external_cache_set("map_search", {"baidu_as_map": {"query": query or "", "city": city or "", "limit": len(out)}}, {"success": True, "items": out})
    return out

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

def _extract_amap_path_points(steps: list) -> list:
    points = []
    for step in steps or []:
        if not isinstance(step, dict):
            continue
        for key in ("polyline", "tmcs", "cities"):
            value = step.get(key)
            if isinstance(value, str):
                for pair in value.split(";"):
                    loc = _extract_coord_pair(pair)
                    if loc:
                        points.append(loc)
            elif isinstance(value, list):
                for sub in value:
                    if isinstance(sub, dict):
                        points.extend(_extract_amap_path_points([sub]))
        for subkey in ("steps", "walking", "bus", "railway"):
            sub = step.get(subkey)
            if isinstance(sub, list):
                points.extend(_extract_amap_path_points(sub))
            elif isinstance(sub, dict):
                points.extend(_extract_amap_path_points([sub]))
    deduped = []
    for p in points:
        if not deduped or abs(deduped[-1]["lat"] - p["lat"]) > 1e-7 or abs(deduped[-1]["lng"] - p["lng"]) > 1e-7:
            deduped.append(p)
    return deduped

def _attach_item_coords(items: list, city: str = "", allow_geocode: bool = True) -> list:
    out = []
    for item in items or []:
        x = dict(item)
        loc = (
            _extract_coord_pair(x)
            or _extract_coord_pair(x.get("location"))
            or _extract_coord_pair(x.get("coordinate"))
            or _extract_coord_pair(x.get("geo"))
        )
        if not loc and allow_geocode:
            query = x.get("address") or x.get("name") or ""
            if query:
                loc = geocode_amap(query, city) or geocode_baidu(query, city)
        if loc:
            x["lat"] = loc["lat"]
            x["lng"] = loc["lng"]
            if loc.get("data_source") == "amap":
                x.setdefault("coord_source", "amap")
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
    "泉州": {"name":"泉州","lat":24.8741,"lng":118.6759,"country":"中国","province":"福建","airport":"泉州晋江机场","rail":"泉州站"},
    "宁德": {"name":"宁德","lat":26.6657,"lng":119.5482,"country":"中国","province":"福建","airport":"福州长乐/温州龙湾机场","rail":"宁德站"},
    "福鼎": {"name":"福鼎","lat":27.3269,"lng":120.2168,"country":"中国","province":"福建","airport":"温州龙湾/福州长乐机场","rail":"福鼎站"},
    "承德": {"name":"承德","lat":40.9515,"lng":117.9634,"country":"中国","province":"河北","airport":"承德普宁机场","rail":"承德南站"},
    "北海": {"name":"北海","lat":21.4811,"lng":109.1202,"country":"中国","province":"广西","airport":"北海福成机场","rail":"北海站"},
    "桂林": {"name":"桂林","lat":25.2736,"lng":110.2900,"country":"中国","province":"广西","airport":"桂林两江机场","rail":"桂林北站"},
    "南宁": {"name":"南宁","lat":22.8170,"lng":108.3669,"country":"中国","province":"广西","airport":"南宁吴圩机场","rail":"南宁东站"},
    "封开": {"name":"封开","lat":23.4242,"lng":111.5123,"country":"中国","province":"广东","airport":"广州白云机场","rail":"肇庆站"},
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
    "Quanzhou": "泉州", "quanzhou": "泉州",
    "Ningde": "宁德", "ningde": "宁德",
    "Fuding": "福鼎", "fuding": "福鼎", "福建福鼎": "福鼎", "宁德福鼎": "福鼎", "福建省宁德市福鼎市": "福鼎", "福鼎市": "福鼎",
    "Chengde": "承德", "chengde": "承德", "河北承德": "承德",
    "Beihai": "北海", "beihai": "北海",
    "Guilin": "桂林", "guilin": "桂林",
    "Nanning": "南宁", "nanning": "南宁",
    "Fengkai": "封开", "fengkai": "封开", "广东封开": "封开", "封开县": "封开",
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
    "泉州": ["泉州", "鲤城", "丰泽", "洛江", "泉港", "晋江", "石狮", "南安", "惠安", "安溪", "清源山", "西街"],
    "宁德": ["宁德", "蕉城", "福安", "福鼎", "霞浦", "古田", "屏南", "周宁", "寿宁", "柘荣", "太姥山", "嵛山岛"],
    "福鼎": ["福鼎", "福鼎市", "宁德福鼎", "福建福鼎", "福建省宁德市福鼎市", "宁德", "太姥山", "嵛山岛", "牛郎岗", "硖门", "桐山", "桐城", "白琳", "点头", "磻溪", "秦屿"],
    "承德": ["承德", "双桥", "双滦", "鹰手营子", "避暑山庄", "普宁寺", "双塔山", "滦河"],
    "北海": ["北海", "海城", "银海", "铁山港", "合浦", "侨港", "涠洲岛", "北部湾"],
    "桂林": ["桂林", "象山", "秀峰", "叠彩", "七星", "雁山", "阳朔", "临桂", "漓江", "东西巷"],
    "南宁": ["南宁", "青秀", "兴宁", "西乡塘", "江南", "良庆", "邕宁", "青秀山", "三街两巷", "中山路"],
    "封开": ["封开", "江口", "南丰", "长岗", "大洲", "广信塔", "龙山", "肇庆"],
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
    "泉州": (24.8741, 118.6759),
    "宁德": (26.6657, 119.5482),
    "福鼎": (27.3269, 120.2168),
    "承德": (40.9515, 117.9634),
    "北海": (21.4811, 109.1202),
    "桂林": (25.2736, 110.2900),
    "南宁": (22.8170, 108.3669),
    "封开": (23.4242, 111.5123),
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

_CROSS_CITY_TERMS_RE = re.compile(
    r"新疆|乌鲁木齐|克拉玛依|国际大巴扎|大理|昆明|丽江|黑油山|合肥|上海|北京|杭州|广州|深圳|成都|重庆|西安|武汉|南京|苏州"
)

def _city_allowed_aliases(city: str) -> list:
    city_key = _guard_city_name(city)
    aliases = list(CITY_KEYWORDS.get(city_key, [city_key] if city_key else []))
    for raw, val in CITY_ALIASES.items():
        if val == city_key:
            aliases.append(str(raw))
    if city_key == "福鼎":
        aliases.extend(["福建福鼎", "宁德福鼎", "福建省宁德市福鼎市", "福鼎市", "宁德", "太姥山", "嵛山岛", "牛郎岗", "硖门", "桐山", "桐城", "白琳", "点头", "磻溪", "秦屿"])
    return list(dict.fromkeys([x for x in aliases if x]))

def _city_guard_text(item: dict, include_query_city: bool = True) -> str:
    if not isinstance(item, dict):
        return str(item or "")
    keys = ("name", "title", "address", "type", "tag", "city", "district", "area", "adname", "province")
    if include_query_city:
        keys = keys + ("query_city",)
    return " ".join([str(item.get(k) or "") for k in keys])

def _candidate_city_matches(item: dict, city: str, allowed_aliases: list = None) -> tuple[bool, str]:
    city_key = _guard_city_name(city)
    if not city_key or city_key in ("本地", "目的地"):
        return True, "no_city"
    aliases = allowed_aliases or _city_allowed_aliases(city_key)
    text = _city_guard_text(item, include_query_city=False)
    explicit_city = _city_alias(str((item or {}).get("city") or ""))
    if explicit_city and explicit_city in CITY_GEO_INDEX:
        if explicit_city == city_key or (city_key == "福鼎" and explicit_city == "宁德") or (city_key == "宁德" and explicit_city == "福鼎"):
            return True, "explicit_city"
        return False, f"city_field:{explicit_city}"
    other = _CROSS_CITY_TERMS_RE.search(text)
    if other and not any(a and a in text for a in aliases):
        return False, f"cross_city_term:{other.group(0)}"
    lat = _coerce_float((item or {}).get("lat") or (item or {}).get("latitude"))
    lng = _coerce_float((item or {}).get("lng") or (item or {}).get("longitude"))
    if lat is not None and lng is not None:
        max_km = 110 if city_key == "福鼎" else (130 if city_key == "宁德" else 80)
        return (is_coord_near_city(lat, lng, city_key, max_km=max_km), "coord")
    if any(a and a in text for a in aliases):
        return True, "alias"
    query_city = _city_alias(str((item or {}).get("query_city") or ""))
    if query_city == city_key or (city_key == "福鼎" and query_city == "宁德"):
        if not other:
            return True, "query_city"
    return False, "city_mismatch"

def city_guard_for_candidates(candidates: list, target_city: str, category: str = "candidate") -> list:
    if not isinstance(candidates, list):
        return []
    city_key = _guard_city_name(target_city)
    aliases = _city_allowed_aliases(city_key)
    print(f"[CANDIDATE_BEFORE_CITY_GUARD] category={category} city={city_key} count={len(candidates)}")
    kept = []
    for item in candidates:
        if not isinstance(item, dict):
            continue
        ok, reason = _candidate_city_matches(item, city_key, aliases)
        if not ok:
            print(f"[CITY_GUARD_DROP] reason=city_mismatch detail={reason} city={city_key} name={item.get('name') or item.get('title') or ''}")
            continue
        guarded = dict(item)
        guarded.setdefault("city", city_key)
        guarded.setdefault("city_guard", "passed")
        kept.append(guarded)
    print(f"[CANDIDATE_AFTER_CITY_GUARD] category={category} city={city_key} count={len(kept)}")
    return kept

def _city_search_label(city: str) -> str:
    city_key = _guard_city_name(city)
    if city_key == "福鼎":
        return "福建福鼎"
    if city_key == "宁德":
        return "福建宁德"
    return city_key or city or ""

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

def _extract_route_waypoints(prompt: str, city_hint: str = "",
                             default_origin: str = "", default_destination: str = "") -> list:
    s = str(prompt or "")
    segment = s
    m = re.search(r"从\s*(.+?)(?:帮我|请你|请|规划|路线|怎么走|，|。|,|$)", s)
    if m:
        segment = m.group(1)
    parts = [
        _clean_place_token(p)
        for p in re.split(r"(?:再到|然后到|接着到|到|去|至|→|->)", segment)
        if _clean_place_token(p)
    ]
    if len(parts) >= 2:
        return parts[:5]
    od = _extract_origin_destination(prompt, city_hint, default_origin, default_destination)
    if od.get("origin") and od.get("destination"):
        return [od["origin"], od["destination"]]
    return []

def _route_city_from_waypoints(waypoints: list) -> str:
    found = []
    for p in waypoints or []:
        m = re.search(_CITY_PAT, str(p or ""))
        if m:
            found.append(_city_alias(m.group(1)))
    if not found:
        return ""
    last = re.search(_CITY_PAT, str((waypoints or [""])[-1]))
    if last:
        return _city_alias(last.group(1))
    return found[0]

def _amap_mode_from_transport(transport: str) -> str:
    s = str(transport or "")
    if re.search(r"打车|自驾|驾车|汽车", s):
        return "driving"
    if re.search(r"骑行|骑车|单车|自行车", s):
        return "riding"
    if re.search(r"地铁|公交|高铁|城际|火车", s):
        return "transit"
    return "walking"

def _plan_amap_route_from_prompt(prompt: str, city: str, origin: dict, dest: dict, transport: str) -> dict:
    mode = _amap_mode_from_transport(transport)
    waypoints = _extract_route_waypoints(
        prompt,
        city,
        origin.get("raw") or origin.get("name") or "",
        dest.get("raw") or dest.get("name") or "",
    )
    if len(waypoints) < 2:
        return {"success": False, "error": "未识别到可规划的高德路线点", **_amap_meta(False, 0)}
    segments, route_points = [], []
    total_m = 0
    total_sec = 0
    for a, b in zip(waypoints, waypoints[1:]):
        seg = route_amap(a, b, mode, city)
        segments.append({"from": a, "to": b, "result": seg})
        if seg.get("success"):
            total_m += int(seg.get("distance_m") or 0)
            total_sec += int(seg.get("duration_sec") or 0)
            pts = _extract_amap_path_points(seg.get("steps") or [])
            route_points.extend(pts)
    ok_segments = [x for x in segments if x["result"].get("success")]
    elapsed = max([x["result"].get("elapsed_ms", 0) for x in ok_segments] or [0])
    return {
        "success": bool(ok_segments),
        "provider": "gaode",
        "engine": "地图引擎",
        "waypoints": waypoints,
        "mode": mode,
        "segments": segments,
        "distance_m": total_m,
        "duration_sec": total_sec,
        "points": route_points,
        **_amap_meta(bool(ok_segments), elapsed, "amap_primary" if ok_segments else ""),
    }

def _amap_coord_from_item(item: dict) -> str:
    lat, lng = _coerce_float((item or {}).get("lat")), _coerce_float((item or {}).get("lng"))
    if lat is None or lng is None:
        loc = _extract_coord_pair((item or {}).get("location"))
        if loc:
            lat, lng = loc.get("lat"), loc.get("lng")
    if lat is None or lng is None:
        return ""
    return f"{float(lng)},{float(lat)}"

def _select_amap_travel_pois(hotels: list, foods: list, sights: list, limit: int = 5) -> list:
    """按旅行动线优先级选择真实/地图 POI：景点开场，餐饮穿插，夜间/住宿收尾。"""
    picked, seen = [], set()
    pools = [
        ("sight", sights or []),
        ("food", foods or []),
        ("sight", (sights or [])[1:]),
        ("food", (foods or [])[1:]),
        ("hotel", hotels or []),
    ]
    for category, items in pools:
        for raw in items:
            name = str((raw or {}).get("name") or "").strip()
            if not name or name in seen:
                continue
            item = dict(raw)
            item.setdefault("category", category)
            if _amap_coord_from_item(item):
                picked.append(item)
                seen.add(name)
                break
        if len(picked) >= limit:
            break
    return picked[:limit]

def _plan_amap_travel_route(city: str, hotels: list, foods: list, sights: list, transport: str) -> dict:
    """高德 POI -> 高德路线规划：为地图卡提供真实 marker/polyline 数据。"""
    if not AMAP_WEBSERVICE_KEY:
        print("🟡 [AMAP_TRAVEL_PLANNER] missing AMAP_WEBSERVICE_KEY")
        _log_amap("AMAP_TRAVEL_PLANNER", False, 0, city=city, interests="", reason="missing_key")
        return {
            "success": False,
            "error": "高德 WebService Key 未配置",
            "message": "高德智能旅游规划需要 AMAP_WEBSERVICE_KEY；当前已切换美团/Mock 兜底。",
            "pois": [],
            **_amap_meta(False, 0),
        }
    if _amap_circuit_open():
        _log_amap("AMAP_TRAVEL_PLANNER", False, 0, city=city, interests="", reason="circuit_open")
        return {
            "success": False,
            "error": AMAP_LAST_ERROR.get("message") or "高德暂不可用",
            "message": AMAP_LAST_ERROR.get("message") or "高德暂不可用，已切换美团/Mock 兜底。",
            "pois": [],
            **_amap_meta(False, 0),
        }
    mode = _amap_mode_from_transport(transport)
    if mode == "transit":
        mode = "driving"
    pois = _select_amap_travel_pois(hotels, foods, sights)
    print("🟢 [AMAP_TRAVEL_PLANNER] city=", city, "interests=", [p.get("name") for p in pois])
    if len(pois) < 2:
        _log_amap("AMAP_TRAVEL_PLANNER", False, 0, city=city, interests=",".join([p.get("name","") for p in pois]), reason="not_enough_pois")
        return {
            "success": False,
            "error": "高德 POI 坐标不足，无法生成旅游路线",
            "message": "高德返回的可用 POI 坐标少于 2 个，已切换美团/Mock 兜底。",
            "pois": pois,
            **_amap_meta(False, 0),
        }
    segments, route_points = [], []
    total_m = 0
    total_sec = 0
    for a, b in zip(pois, pois[1:]):
        origin_coord = _amap_coord_from_item(a)
        dest_coord = _amap_coord_from_item(b)
        seg = route_amap(origin_coord, dest_coord, mode, city)
        segments.append({"from": a.get("name"), "to": b.get("name"), "mode": mode, "result": seg})
        if seg.get("success"):
            total_m += int(seg.get("distance_m") or 0)
            total_sec += int(seg.get("duration_sec") or 0)
            pts = seg.get("points") or _extract_amap_path_points(seg.get("steps") or [])
            if pts:
                route_points.extend(pts)
            else:
                for item in (a, b):
                    lat, lng = _coerce_float(item.get("lat")), _coerce_float(item.get("lng"))
                    if lat is not None and lng is not None:
                        route_points.append({"lat": lat, "lng": lng})
    ok_segments = [x for x in segments if x["result"].get("success")]
    elapsed = max([x["result"].get("elapsed_ms", 0) for x in ok_segments] or [0])
    print("🟢 [AMAP_ROUTE] route_points=", route_points)
    _log_amap(
        "AMAP_TRAVEL_PLANNER",
        bool(ok_segments),
        elapsed,
        city=city,
        interests=",".join([p.get("name","") for p in pois]),
        count=len(pois),
    )
    return {
        "success": bool(ok_segments),
        "error": "" if ok_segments else "高德路线段规划失败",
        "message": "" if ok_segments else "高德 POI 已获取，但路线段规划未成功，已保留地图链接并切换美团/Mock 兜底。",
        "provider": "gaode",
        "engine": "地图引擎",
        "mode": mode,
        "pois": pois,
        "segments": segments,
        "distance_m": total_m,
        "duration_sec": total_sec,
        "points": route_points,
        **_amap_meta(bool(ok_segments), elapsed, "amap_travel_planner" if ok_segments else ""),
    }

def _resolve_place_info(name: str, city_hint: str = "") -> dict:
    raw = _clean_place_token(name) or _clean_place_token(city_hint) or "当前位置"
    key = _city_alias(raw)
    if key in CITY_GEO_INDEX:
        info = dict(CITY_GEO_INDEX[key])
        info["raw"] = raw
        return info
    a = geocode_amap(key, city_hint)
    if a:
        return {
            "name": key, "raw": raw, "lat": a["lat"], "lng": a["lng"],
            "country": "中国", "province": "", "airport": f"{key}机场", "rail": f"{key}站",
            "source": "amap_geocode",
        }
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
    gaode_url = _amap_map_link(
        f"https://www.amap.com/dir?from[name]={o}&to[name]={d}&type=bus",
        city=dest.get("name") or "",
        origin=origin.get("name") or "",
        destination=dest.get("name") or "",
    )
    return {
        "baidu": f"https://map.baidu.com/dir/?origin=name:{o}&destination=name:{d}&mode=transit&output=html",
        "gaode": gaode_url,
        "google": f"https://www.google.com/maps/dir/{o}/{d}/?travelmode=transit",
        "flight": f"https://www.google.com/travel/flights?q=Flights%20from%20{o}%20to%20{d}",
    }

def _amap_map_link(url: str, **meta) -> str:
    t0 = time.perf_counter()
    elapsed = round((time.perf_counter() - t0) * 1000)
    _log_amap("AMAP_MAP_LINK", bool(url), elapsed, **meta)
    return url

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
    amap_route = _plan_amap_route_from_prompt(user_prompt, dest.get("name") or city, start, dest, decision.get("priority", ""))
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
        "amap_route": amap_route,
        "map_engine": "地图路线引擎" if amap_route.get("success") else "地图链接备用",
        "route_source": "amap_primary" if amap_route.get("success") else "map_link_only",
        "poi_source": "地图参考",
        "flight_query": flight_query,
        "status_flow": status_flow,
        "long_distance": long_legs,
        "local_transfer": local_legs,
        "short_backup": backup_legs,
        "weather": _weather_aux(dest.get("name") or city),
        "data_layer": {
            "geo": "known_city_or_geocode",
            "distance": "haversine",
            "route": "amap" if amap_route.get("success") else "map_link_only",
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
        for alias in sorted(CITY_ALIASES, key=len, reverse=True):
            if alias and alias in s:
                destination = _city_alias(alias)
                break
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
    wants_meituan = _requires_meituan_real_resources(s) and not avoid_meituan
    requires_real_meituan = bool(re.search(r"查看真实商户|真实(?:的)?(?:美团)?(?:店名|酒店|商家|评分|人均)|美团上真实|真实美团|美团.*真实", s)) and not avoid_meituan
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
    destination = _guard_city_name(dest or od.get("destination") or _clean_place_token(city_hint) or "本地")
    return {
        "origin": origin,
        "origin_is_default": _origin_is_default,
        "destination": destination,
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

def _detect_message_destination(text: str) -> str:
    points = _extract_trip_points(str(text or ""), "")
    dest = _city_alias(points.get("destination", ""))
    if dest and dest != "本地":
        return dest
    s = str(text or "")
    for pat in (
        r"(?:帮我规划|规划|帮我安排|安排)\s*([^#，。！？,;；\s]{2,12})(?:一日游|两日游|三日游|[0-9一二两三四五六七八九十]{1,3}\s*天|行程|攻略|旅游|旅行|玩|$)",
        r"([^#，。！？,;；\s]{2,12})(?:一日游|两日游|三日游|[0-9一二两三四五六七八九十]{1,3}\s*日游)",
    ):
        m2 = re.search(pat, s)
        if m2:
            cand = _city_alias(_clean_place_token(m2.group(1)))
            if _is_valid_place_name(cand):
                return cand
    m = re.search(_CITY_PAT, str(text or ""))
    return _city_alias(m.group(1)) if m else ""

def _resolve_agent_city(raw_message: str, request_city: str, task_state: dict) -> tuple[str, str]:
    detected = _detect_message_destination(raw_message)
    if detected:
        return detected, detected
    state_city = _city_alias((task_state or {}).get("destination") or (task_state or {}).get("active_destination") or (task_state or {}).get("city") or (task_state or {}).get("active_city") or "")
    if state_city:
        return "", state_city
    req_city = _city_alias(_clean_place_token(request_city))
    if req_city:
        return "", req_city
    return "", "上海"

def _resolve_agent_city_for_route_card(raw_message: str, request_city: str,
                                       task_state: dict, body_coords: dict = None) -> tuple[str, str, str]:
    """路线地图卡城市优先级：本轮明确目的地 > 当前位置 > 当前任务/请求城市。"""
    detected, resolved = _resolve_agent_city(raw_message, request_city, task_state)
    if detected:
        return detected, resolved, "explicit_destination"
    if body_coords and _looks_meituan_trip(raw_message) and not _is_followup_msg(raw_message, task_state or {}):
        loc_city = _nearest_city_from_coords(float(body_coords["lat"]), float(body_coords["lng"]), "")
        if loc_city:
            return "", loc_city, "current_location"
    return detected, resolved, "task_or_request_city"

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

def _build_intent_understanding_card(req: dict, persona_state: dict,
                                     decision: dict, prompt: str = "") -> dict:
    text = str(prompt or "")
    prefs = []
    if re.search(r"吃好|美食|餐厅|本地菜|小吃|米其林|夜市|早餐|甜品|咖啡", text):
        prefs.append("美食优先")
    if re.search(r"不想太累|别太累|松弛|慢|不赶|舒适|放松|慢逛|休息", text):
        prefs.append("不要太累")
    if re.search(r"拍照|出片|日落|夜景|打卡|好看", text):
        prefs.append("拍照/夜景优先")
    if re.search(r"安静|人少|避开人群|不想排队|社恐", text):
        prefs.append("避开人流与排队")
    if re.search(r"省钱|便宜|穷游|预算少|性价比|免费", text):
        prefs.append("预算敏感")
    if req.get("wants_meituan") or req.get("requires_real_meituan"):
        prefs.append("需要平台真实资源")
    if (req.get("user_preference") or {}).get("avoid_meituan"):
        prefs.append("避开美团下单")
    if not prefs:
        prefs.append("适合周末放松")
    days = max(1, int(req.get("days") or 1))
    time_text = f"{days}天{days - 1}晚" if days > 1 else "1日短途游"
    labels = [str(x).replace("状态", "").replace("模式", "") for x in (persona_state.get("labels") or []) if x]
    planning_style = " + ".join(labels) if labels else "松弛感"
    return {
        "title": "我理解你的需求",
        "destination": req.get("destination") or "目的地",
        "time": time_text,
        "budget": f"约 ¥{req.get('budget') or 0}",
        "preferences": list(dict.fromkeys(prefs))[:5],
        "planning_style": planning_style,
        "transport": _transport_default_label(decision),
        "locked_fields": {
            "destination": req.get("destination") or "",
            "days": days,
            "budget": req.get("budget") or 0,
            "commerce_mode": req.get("commerce_mode", ""),
            "planner_mode": req.get("planner_mode", ""),
        },
        "source": "deepseek_intent_lock",
    }

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
    core = re.search(r"行程|攻略|规划|安排|预算|酒店|住宿|宾馆|民宿|美团|景点|门票|一日游|两日游|三日游|周末游|[0-9一二两三四五六七八九十]{1,3}\s*天|去.+玩|旅游|旅行|游玩", s)
    return bool(core and re.search(r"去|到|前往|玩|行程|规划|安排|预算|酒店|住宿|美团|景点", s))

MEITUAN_REAL_INTENT_RE = re.compile(
    r"美团上|美团|团购|优惠券?|订酒店|酒店预订|美团酒店|美团餐厅|美团下单|查看真实商户|"
    r"真实店名|真实评分|真实人均|门票团购",
    re.I,
)

def _requires_meituan_real_resources(text: str) -> bool:
    s = str(text or "")
    if re.search(r"不想在美团|不要美团|不用美团|不想用美团|不在美团", s):
        return False
    return bool(MEITUAN_REAL_INTENT_RE.search(s))

def _looks_direct_meituan_resource(text: str) -> bool:
    s = str(text or "")
    if not _requires_meituan_real_resources(s):
        return False
    if re.search(r"行程|规划|攻略|[0-9一二两三四五六七八九十]{1,3}\s*天|旅游|旅行|游玩|去.+玩", s):
        return False
    has_resource = re.search(r"酒店|住宿|宾馆|民宿|餐厅|美食|吃饭|好吃|外卖|团购|券|优惠|跑腿|帮送|真实店名|真实评分|真实人均|真实商户|商家|门票", s)
    return bool(has_resource)

def _looks_public_facility_search(text: str) -> bool:
    """明确公共设施意图：只走地图 POI，不触发美团/米其林/黑珍珠。"""
    s = str(text or "")
    if re.search(r"厕所|卫生间|洗手间|公厕|公共厕所|茅厕|厕所在哪|找厕所", s):
        return True
    return bool(re.search(r"restroom|toilet|washroom|bathroom|\bwc\b", s, flags=re.I))

def _looks_direct_amap_route(text: str) -> bool:
    s = str(text or "")
    if re.search(r"一日游|旅游|旅行|游玩|行程|攻略|预算|酒店|住宿", s):
        return False
    return bool(re.search(r"怎么走|怎么去|导航|路线|从.+到", s) and re.search(r"到|去|至|→|->", s))

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
    # 打车 / 机票 等明确单点动作（最高优先）
    if re.search(r"打车|叫车|网约车|出租车|接驳|机票|航班|飞机票|订机票|买机票", s):
        return True
    # 高铁/火车票：需带明确订票信号，避免抢走"坐高铁去X玩"这类行程规划
    if re.search(r"高铁|火车票|动车|城际", s) and re.search(r"订|买|预订|预定|票|出票|下单", s):
        return True
    # 酒店/门票/景点/餐厅：需带明确下单动词（订/预订/预定/买…），避免抢走行程规划
    if re.search(r"(?:订|预订|预定|帮我订|要订|想订|代订|下单|买)[^。，,；;\n]{0,12}(?:酒店|房间|房|民宿|宾馆|客栈|门票|景点|景区|餐厅|餐|座位|位子|位)", s):
        return True
    # 排队监控：需明确监控/提醒意图；「不想排队」是行程偏好，不能触发；行程规划句也不触发
    is_trip = re.search(r"玩.{0,4}天|去.+玩|行程|规划|一日游|两日游|三日游|周末|citywalk|周边游|带.{0,3}(?:爸妈|父母|孩子|娃|家人)", s)
    if re.search(r"监控|提醒我|后台盯|盯一下|盯着|帮我盯", s) and re.search(r"排队|等位|有位|满座|人多", s):
        return True
    if re.search(r"排队|等位|有位|满座|人多", s) and not is_trip and not re.search(r"不想|不要|不排|少排|怕|避免|讨厌", s):
        return True
    return False

def _mock_resource_final_text(results: list) -> str:
    lines = ["🍊 已启动资源编排："]
    for item in results:
        tool = item.get("tool")
        result = item.get("result", {})
        if tool == "mock_start_service_monitor":
            mon = result.get("monitor", {})
            latest = mon.get("latest", {})
            lines.append(f"- 后台监控：{mon.get('target_name','目标资源')}，{latest.get('message','已开始监控')}，建议：{latest.get('recommended_action','继续观察')}")
        elif tool == "amap_poi":
            rows = result.get("results") or []
            scope = "你当前位置附近" if result.get("by_location") else result.get("city", "")
            if rows:
                lines.append(f"- {scope}真实备选餐厅（高德实时，排队过久可直接切换）：")
                for r in rows[:5]:
                    dist = r.get("distance")
                    dist_txt = f"，约{dist}米" if dist else ""
                    rating = r.get("rating")
                    rate_txt = f"，评分{rating}" if rating else ""
                    lines.append(f"  · {r.get('name','')}（{r.get('address','')}{dist_txt}{rate_txt}）")
            else:
                lines.append(f"- {scope}暂未搜到真实备选餐厅，可扩大范围或稍后重试（未使用模板数据）。")
        elif tool == "mock_request_ride":
            q = result.get("quote", {})
            oid = result.get("order", {}).get("order_id", "")
            lines.append(f"- 打车待确认：{q.get('origin','')} → {q.get('destination','')}，约{q.get('eta_minutes','-')}分钟到达，预估¥{q.get('price_estimate','-')}，订单 {oid}")
        elif tool == "mock_search_flights":
            rec = result.get("recommended", {})
            lines.append(f"- Mock 航班待确认：{result.get('origin','')} → {result.get('destination','')}，推荐 {rec.get('flight_no','')} {rec.get('depart_time','')}起飞 ¥{rec.get('price','-')}，确认后 Mock 出票")
        elif tool == "mock_book_train":
            t = result.get("train", {})
            oid = result.get("order", {}).get("order_id", "")
            lines.append(f"- 高铁待确认：{t.get('train_no','')} {t.get('seat_class','')}，{t.get('depart_time','')}发车，¥{t.get('price','-')}，订单 {oid}")
        elif tool == "mock_book_resource":
            m = result.get("merchant", {})
            oid = result.get("order", {}).get("order_id", "")
            lines.append(f"- {result.get('order',{}).get('item',{}).get('category','资源')}待确认：{m.get('name','')}，¥{m.get('price','-')}，订单 {oid}")
    lines.append("所有订单均为待确认状态，只有你点击确认后才会进入模拟下单。🍊")
    return "\n".join(lines)

def _rule_mock_resource_agent_response(user_message: str, city_hint: str = "上海",
                                       persona: str = "", map_provider: str = "",
                                       body_coords: dict = None) -> Response:
    def generate():
        req = _extract_trip_requirements(user_message, city_hint)
        # 位置优先级（要求）：用户明确想去的地方 > 当前定位 > 请求城市；绝不默认套模板城市。
        # 只认本轮文本里真正点名的目的地，避免 city_hint 默认值(如"上海")冒充明确意愿。
        explicit_dest = extract_city_from_message(user_message)
        if explicit_dest:
            city = explicit_dest
            search_location = ""              # 有明确意愿 → 按地名查
        elif body_coords:
            city = _nearest_city_from_coords(float(body_coords["lat"]), float(body_coords["lng"]), city_hint) or city_hint
            search_location = f"{float(body_coords['lng'])},{float(body_coords['lat'])}"  # 兜底 → 按当前位置查
        else:
            city = city_hint
            search_location = ""
        origin = req.get("origin") or city_hint or "当前位置"
        destination = explicit_dest or city or "目的地"
        results = []
        idx = 1
        if re.search(r"排队|等位|有位|满座|监控|提醒我|后台盯|人多", user_message):
            args = {
                "resource_type": "queue",
                "target_name": explicit_dest or "你正在排队的餐厅",
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
            # 备选餐厅必须是真实 POI：有明确意愿按地名查，否则按当前位置查附近，绝不用模板/Mock 数据
            backup_items = search_amap_place("餐厅", city, 5,
                                             location=search_location,
                                             radius=2000 if search_location else 3000)
            backup_payload = {
                "success": bool(backup_items),
                "city": city,
                "keyword": "备选餐厅",
                "by_location": bool(search_location),
                "results": backup_items,
                "count": len(backup_items),
                "data_source": "amap",
                "tool_name": "amap-lbs-skill",
            }
            yield f"data: {json.dumps({'type':'step_start','id':idx,'tool':'amap_poi','input':{'city':city,'keyword':'备选餐厅','location':search_location}}, ensure_ascii=False)}\n\n"
            yield f"data: {json.dumps({'type':'step_done','id':idx,'tool':'amap_poi','result':backup_payload,'summary':_tool_summary('amap_poi', {'city':city,'keyword':'备选餐厅'}, backup_payload)}, ensure_ascii=False)}\n\n"
            results.append({"tool": "amap_poi", "result": backup_payload})
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
        if re.search(r"高铁|火车票|动车|订高铁|买高铁|高铁票", user_message):
            od = _extract_origin_destination(user_message, city_hint, origin, destination)
            args = {
                "origin": od.get("origin") or origin,
                "destination": od.get("destination") or destination,
                "date": "",
                "seat_class": "二等座",
                "passengers": 1,
                "user_context": {"persona": persona, "budget": req.get("budget"), "city": city},
            }
            yield f"data: {json.dumps({'type':'step_start','id':idx,'tool':'mock_book_train','input':args}, ensure_ascii=False)}\n\n"
            tr = tool_mock_book_train(**args)
            yield f"data: {json.dumps({'type':'step_done','id':idx,'tool':'mock_book_train','result':tr,'summary':_tool_summary('mock_book_train', args, tr)}, ensure_ascii=False)}\n\n"
            results.append({"tool": "mock_book_train", "result": tr})
            idx += 1
        booking_kind = None
        if re.search(r"酒店|住宿|民宿|宾馆|客栈|订房|订间房", user_message):
            booking_kind = "hotel"
        elif re.search(r"门票|景点|景区|景区票|订票|游园", user_message):
            booking_kind = "ticket"
        elif re.search(r"订餐|订座|订位|位子|(?:订|预订|预定|帮我订|要订|想订|代订)[^。，,；;\n]{0,6}(?:餐厅|餐馆|饭店|餐)", user_message):
            # 仅在有明确订座动词时才生成 Mock 订单；"备选餐厅/热门餐厅"等不触发，避免冒出模板数据
            booking_kind = "restaurant"
        if booking_kind:
            args = {
                "booking_kind": booking_kind,
                "city": city,
                "keyword": "",
                "user_context": {"persona": persona, "budget": req.get("budget"), "city": city},
            }
            yield f"data: {json.dumps({'type':'step_start','id':idx,'tool':'mock_book_resource','input':args}, ensure_ascii=False)}\n\n"
            tr = tool_mock_book_resource(**args)
            yield f"data: {json.dumps({'type':'step_done','id':idx,'tool':'mock_book_resource','result':tr,'summary':_tool_summary('mock_book_resource', args, tr)}, ensure_ascii=False)}\n\n"
            results.append({"tool": "mock_book_resource", "result": tr})
            idx += 1
        if re.search(r"打车|叫车|网约车|出租车|接驳", user_message):
            taxi_body = {
                "city": city,
                "user_query": user_message,
                "userLocation": body_coords,
                "user_context": {"persona": persona, "budget": req.get("budget"), "city": city},
            }
            resolved_taxi = _resolve_mock_taxi_request(taxi_body, city, user_message)
            if not resolved_taxi.get("success"):
                yield f"data: {json.dumps({'type':'final','text':resolved_taxi.get('error') or '打车信息待确认。'}, ensure_ascii=False)}\n\n"
                return
            args = {
                "origin": resolved_taxi["origin"],
                "destination": resolved_taxi["destination"],
                "city": resolved_taxi.get("city") or city,
                "trigger_reason": user_message,
                "user_context": resolved_taxi.get("user_context") or {"persona": persona, "budget": req.get("budget"), "city": city},
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
    elif re.search(r"景点|门票|玩什么|去哪玩", s):
        intent, keyword = "ticket_search", "景点"
    elif re.search(r"美食|好吃|吃饭|餐厅|饭店", s):
        intent, keyword = "restaurant_search", "附近美食" if nearby_with_coords else "美食"
    else:
        intent, keyword = "restaurant_search", "附近美食" if nearby_with_coords else "餐厅"
    filters = {}
    price_high = _extract_price_high(s)
    if price_high:
        filters["price_high"] = price_high
    if nearby_with_coords:
        filters.update({"sort_by": "distance", "distance_radius": 5000})
    city = _detect_message_destination(s) or req.get("destination") or city_hint
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

def _direct_public_facility_input(text: str, city_hint: str = "") -> dict:
    s = str(text or "")
    coords = _parse_lat_lng(s)
    detected_city = _detect_message_destination(s)
    req = _extract_trip_requirements(s, city_hint)
    city = detected_city or req.get("destination") or city_hint or ""
    if coords and not detected_city:
        city = _nearest_city_from_coords(coords["lat"], coords["lng"], city) or city
    location = f"{coords['lng']},{coords['lat']}" if coords else ""
    explicit_radius = 0
    rm = re.search(r"(?:扩大到|半径|范围)\s*([0-9]+(?:\.[0-9]+)?)\s*(公里|千米|km|KM|米|m)?", s)
    if rm:
        unit = (rm.group(2) or "米").lower()
        value = float(rm.group(1))
        explicit_radius = int(value * 1000) if unit in ("公里", "千米", "km") else int(value)
    keyword = "公共厕所"
    if re.search(r"商场|购物中心|商圈", s):
        keyword = "商场"
    elif re.search(r"地铁|轨道交通|车站", s):
        keyword = "地铁站"
    elif re.search(r"景区|景点|公园", s):
        keyword = "景区"
    return {
        "city": city,
        "keyword": keyword,
        "location": location,
        "radius": explicit_radius if explicit_radius else (500 if location else 0),
        "explicit_radius": explicit_radius,
        "limit": 8,
        "user_lat": coords.get("lat") if coords else None,
        "user_lng": coords.get("lng") if coords else None,
    }

def _amap_keyword_from_resource_args(args: dict) -> str:
    intent = str((args or {}).get("intent") or "")
    keyword = str((args or {}).get("keyword") or "").strip()
    if intent == "hotel_search":
        return "酒店"
    if intent == "ticket_search":
        return "景点"
    if intent == "group_buy_query":
        return "团购"
    if "外卖" in keyword:
        return "餐厅"
    return keyword.replace("附近", "") or "美食"

def _amap_poi_payload(city: str, keyword: str, results: list, elapsed_ms: int = 0) -> dict:
    ok = bool(results)
    return {
        "success": ok,
        "data_source": "amap",
        "tool_name": "amap-lbs-skill",
        "elapsed_ms": int(elapsed_ms or (results[0].get("elapsed_ms", 0) if results else 0) or 0),
        "city": city,
        "keyword": keyword,
        "count": len(results or []),
        "results": results or [],
        "source": "amap",
        "fallback": not ok,
        "message": "" if ok else "⚠️ 地图路线暂未返回，已启用备用方案",
    }

def _amap_map_url_for_route(waypoints: list, city: str = "") -> str:
    if len(waypoints or []) < 2:
        return _amap_map_link(f"https://www.amap.com/search?query={quote(city or '地图')}", city=city)
    start = quote(str(waypoints[0] or ""))
    end = quote(str(waypoints[-1] or ""))
    return _amap_map_link(
        f"https://www.amap.com/dir?from[name]={start}&to[name]={end}&type=walk",
        city=city,
        origin=waypoints[0],
        destination=waypoints[-1],
    )

def _amap_route_payload(user_message: str, city_hint: str = "") -> tuple[dict, dict]:
    waypoints = _extract_route_waypoints(user_message, city_hint)
    detected_city = _detect_message_destination(user_message)
    if detected_city and not (re.search(_CITY_PAT, detected_city) or detected_city in CITY_GEO_INDEX):
        detected_city = ""
    city = _route_city_from_waypoints(waypoints) or detected_city or _city_alias(city_hint) or "上海"
    mode = _amap_mode_from_transport(user_message)
    segments, route_points = [], []
    total_m = 0
    total_sec = 0
    for a, b in zip(waypoints, waypoints[1:]):
        seg = route_amap(a, b, mode, city)
        segments.append({"from": a, "to": b, "mode": mode, "result": seg})
        if seg.get("success"):
            total_m += int(seg.get("distance_m") or 0)
            total_sec += int(seg.get("duration_sec") or 0)
            route_points.extend(seg.get("points") or [])
    ok_segments = [x for x in segments if x["result"].get("success")]
    elapsed = max([x["result"].get("elapsed_ms", 0) for x in ok_segments] or [0])
    link = _amap_map_url_for_route(waypoints, city)
    result = {
        "success": bool(ok_segments),
        "data_source": "amap",
        "tool_name": "amap-lbs-skill",
        "elapsed_ms": int(elapsed or 0),
        "city": city,
        "mode": mode,
        "waypoints": waypoints,
        "segments": segments,
        "route_points": route_points,
        "points": route_points,
        "distance_m": total_m,
        "duration_sec": total_sec,
        "map_url": link,
        "route_source": "amap_primary" if ok_segments else "amap_failed",
        "fallback": not bool(ok_segments),
        "message": "" if ok_segments else "⚠️ 地图路线暂未返回，已启用备用方案",
    }
    link_result = {
        "success": bool(link),
        "data_source": "amap",
        "tool_name": "amap-lbs-skill",
        "elapsed_ms": 0,
        "city": city,
        "map_url": link,
        "waypoints": waypoints,
    }
    return result, link_result

def _resource_fusion_fallback_text(user_message: str, amap_result: dict, meituan_result: dict) -> str:
    city = amap_result.get("city") or meituan_result.get("city") or "目的地"
    kw = amap_result.get("keyword") or meituan_result.get("keyword") or "资源"
    amap_names = [x.get("name") for x in (amap_result.get("results") or [])[:3] if x.get("name")]
    mt_names = [x.get("name") for x in (meituan_result.get("results") or [])[:3] if x.get("name")]
    lines = [f"🍊 已为你融合地图参考和美团搜索结果：{city}{kw}。"]
    if amap_names:
        lines.append("地图参考：" + "、".join(amap_names))
    if mt_names:
        lines.append("美团搜索：" + "、".join(mt_names))
    if not amap_names and not mt_names:
        lines.append("⚠️ 地图路线暂未返回，已启用备用方案；当前没有足够真实商户，建议稍后重试或换关键词。")
    return "\n".join(lines)

def _deepseek_resource_fusion_text(user_message: str, amap_result: dict, meituan_result: dict) -> str:
    if not _has_any_llm():
        return _resource_fusion_fallback_text(user_message, amap_result, meituan_result)
    t0 = time.perf_counter()
    try:
        resp = _llm_chat_completion({
            "temperature": 0.2,
            "max_tokens": 700,
            "messages": [
                {"role": "system", "content": "你是马到橙功本地生活 Agent。基于高德和美团 JSON 结果做融合总结；优先使用真实商户名，不伪造店名。输出中文短段落，不要 Markdown 表格。"},
                {"role": "user", "content": json.dumps({
                    "user_request": user_message,
                    "amap_result": amap_result,
                    "meituan_result": meituan_result,
                }, ensure_ascii=False)}
            ],
        }, purpose="resource_fusion")
        text = ((resp.json().get("choices") or [{}])[0].get("message") or {}).get("content", "")
        return _clean_markdown(text) or _resource_fusion_fallback_text(user_message, amap_result, meituan_result)
    except Exception as e:
        _record_tool_call("llm", "timeout" if "timeout" in str(e).lower() else "error", round((time.perf_counter() - t0) * 1000), purpose="resource_fusion")
        return _resource_fusion_fallback_text(user_message, amap_result, meituan_result)

_TOILET_PRIORITY = {
    "厕所": 0,
    "公共卫生间": 0,
    "商场": 1,
    "地铁站": 2,
    "地铁站/车站": 2,
    "车站": 2,
    "加油站": 3,
    "公园": 4,
    "图书馆": 4,
    "社区中心": 4,
    "游客中心": 4,
    "景点服务区": 4,
    "咖啡店": 5,
    "餐饮中心": 5,
    "餐厅": 5,
    "便利店": 5,
    "学校": 6,
    "高校": 6,
}

def _toilet_walk_minutes(distance_m) -> int:
    try:
        return max(1, int(round(float(distance_m) / 75)))
    except Exception:
        return 0

def _toilet_place_type(item: dict) -> str:
    text = " ".join(str((item or {}).get(k) or "") for k in ("type", "facility_query", "name"))
    if re.search(r"公共卫生间|公共厕所|卫生间|厕所|restroom|toilet|washroom|bathroom", text, flags=re.I):
        return "厕所"
    if re.search(r"商场|购物中心|mall", text, flags=re.I):
        return "商场"
    if re.search(r"地铁|MRT|metro|subway|车站|station", text, flags=re.I):
        return "地铁站"
    if re.search(r"加油|petrol|gas|fuel", text, flags=re.I):
        return "加油站"
    if re.search(r"公园|park", text, flags=re.I):
        return "公园"
    if re.search(r"图书馆|library", text, flags=re.I):
        return "图书馆"
    if re.search(r"社区|community", text, flags=re.I):
        return "社区中心"
    if re.search(r"游客|tourist|景点服务|information", text, flags=re.I):
        return "游客中心"
    if re.search(r"咖啡|cafe|coffee", text, flags=re.I):
        return "咖啡店"
    if re.search(r"便利|convenience", text, flags=re.I):
        return "便利店"
    if re.search(r"餐饮|餐厅|饭店|hawker|food court|restaurant", text, flags=re.I):
        return "餐饮中心"
    if re.search(r"学校|高校|大学|学院|school|university|college", text, flags=re.I):
        return "高校"
    return str((item or {}).get("facility_query") or (item or {}).get("type") or "可尝试地点")

def _toilet_confidence(place_type: str) -> str:
    if place_type == "厕所":
        return "高"
    if place_type in ("商场", "地铁站", "加油站", "公园", "图书馆", "社区中心", "游客中心"):
        return "中"
    return "低"

def _toilet_note(place_type: str) -> str:
    if place_type == "厕所":
        return "明确厕所，开放情况以现场为准"
    if place_type == "商场":
        return "商场内通常有卫生间，需现场确认"
    if place_type == "地铁站":
        return "可能有公共卫生间，可询问工作人员"
    if place_type == "加油站":
        return "加油站通常可尝试借用，需现场确认"
    if place_type == "公园":
        return "公园可能设有公共卫生间，需现场确认"
    if place_type == "高校":
        return "可能有卫生间，部分高校入校需要申请"
    return "可能有卫生间，需现场确认"

def _toilet_sort_key(item: dict) -> tuple:
    place_type = _toilet_place_type(item)
    try:
        dist = int(float((item or {}).get("distance") or (item or {}).get("distance_m") or 999999))
    except Exception:
        dist = 999999
    return (_TOILET_PRIORITY.get(place_type, 9), dist)

def _normalize_toilet_results(items: list, user_lat=None, user_lng=None, limit: int = 3) -> list:
    normalized = []
    seen = set()
    for item in items or []:
        if not isinstance(item, dict):
            continue
        loc = _extract_coord_pair(item.get("location")) or _extract_coord_pair(item)
        lat = _coerce_float((loc or {}).get("lat") if loc else item.get("lat"))
        lng = _coerce_float((loc or {}).get("lng") if loc else item.get("lng"))
        dist = item.get("distance") if item.get("distance") not in (None, "") else item.get("distance_m")
        if (dist in (None, "")) and user_lat is not None and user_lng is not None and lat is not None and lng is not None:
            dist = round(_haversine(float(user_lat), float(user_lng), float(lat), float(lng)) * 1000)
        try:
            distance_m = int(round(float(dist))) if dist not in (None, "") else 0
        except Exception:
            distance_m = 0
        name = str(item.get("name") or "").strip()
        place_type = _toilet_place_type(item)
        if not name:
            name = "公共卫生间" if place_type == "厕所" else place_type
        key = (name, round(float(lat or 0), 5), round(float(lng or 0), 5))
        if key in seen:
            continue
        seen.add(key)
        map_url = ""
        if lat is not None and lng is not None:
            map_url = _amap_map_link(
                f"https://uri.amap.com/marker?position={float(lng)},{float(lat)}&name={quote(name)}&src=madao&callnative=1"
            )
        elif name:
            map_url = _amap_map_link(f"https://uri.amap.com/search?keyword={quote(name)}&src=madao&callnative=1")
        normalized.append({
            "name": name,
            "place_type": place_type,
            "distance_m": distance_m,
            "walk_minutes": _toilet_walk_minutes(distance_m),
            "address": str(item.get("address") or "").strip(),
            "confidence": _toilet_confidence(place_type),
            "note": _toilet_note(place_type),
            "lat": lat,
            "lng": lng,
            "map_url": map_url,
        })
    normalized.sort(key=lambda x: (_TOILET_PRIORITY.get(x.get("place_type"), 9), x.get("distance_m") or 999999))
    return normalized[:max(1, int(limit or 3))]

def _nearby_toilet_reply_payload(args: dict, items: list) -> dict:
    results = _normalize_toilet_results(
        items,
        (args or {}).get("user_lat"),
        (args or {}).get("user_lng"),
        3,
    )
    return {
        "reply_type": "nearby_toilet_results",
        "title": "附近厕所/卫生间",
        "location": {
            "lat": (args or {}).get("user_lat"),
            "lng": (args or {}).get("user_lng"),
        },
        "results": results,
        "actions": [
            {"label": "导航过去", "action_type": "open_map_route", "payload": {}, "requires_confirm": False},
            {"label": "换一个", "action_type": "show_next_toilet_option", "payload": {}, "requires_confirm": False},
            {"label": "扩大范围", "action_type": "expand_toilet_search", "payload": {}, "requires_confirm": False},
        ],
    }

def _public_facility_fallback_text(user_message: str, poi_result: dict) -> str:
    payload = (poi_result or {}).get("reply_payload") or {}
    if not payload:
        payload = _nearby_toilet_reply_payload({}, (poi_result or {}).get("results") or [])
    results = payload.get("results") or []
    if results:
        explicit = any(x.get("place_type") == "厕所" for x in results)
        header = "🚻 找到附近厕所" if explicit else "🚻 附近没有查到明确公共厕所，我先帮你找了最可能有卫生间的地点"
        lines = [header]
        has_school = False
        for i, item in enumerate(results[:3], 1):
            place_type = item.get("place_type") or ""
            if place_type == "高校":
                has_school = True
            dist = item.get("distance_m") or 0
            dist_text = f"距离约 {dist} 米 · 步行约 {item.get('walk_minutes') or _toilet_walk_minutes(dist)} 分钟" if dist else "距离以地图为准"
            address = item.get("address") or "地址待现场确认"
            lines.append(
                f"\n{i}. {item.get('name','')}"
                f"\n{dist_text}"
                f"\n地址：{address}"
                f"\n可信度：{item.get('confidence','中')}"
                f"\n说明：{item.get('note','可能有卫生间，需现场确认')}"
            )
        if has_school:
            lines.append("\n🔔 部分高校入校需要申请，建议优先选择商场、地铁站或开放式公共场所。")
        lines.append("\n可点“导航过去”，也可以换一个或扩大范围。")
        return "\n".join(lines)
    return (
        "🚻 我还没有拿到可导航的附近地点。\n"
        "请开启定位，或直接发送：找厕所 [纬度x, 经度y]。"
    )

def _deepseek_public_facility_text(user_message: str, poi_result: dict) -> str:
    if not _has_any_llm():
        return _public_facility_fallback_text(user_message, poi_result)
    t0 = time.perf_counter()
    try:
        resp = _llm_chat_completion({
            "temperature": 0.2,
            "max_tokens": 550,
            "messages": [
                {"role": "system", "content": "你是马到橙功本地生活 Agent。用户正在找厕所/卫生间。你只能基于附近地点结果整理回复，禁止提美团、米其林、黑珍珠，禁止伪造店名，禁止出现 POI/API/接口 等技术词。输出中文短回复。"},
                {"role": "user", "content": json.dumps({
                    "user_request": user_message,
                    "public_facility_search": poi_result,
                }, ensure_ascii=False)}
            ],
        }, purpose="public_facility_summary")
        text = ((resp.json().get("choices") or [{}])[0].get("message") or {}).get("content", "")
        return _clean_markdown(text) or _public_facility_fallback_text(user_message, poi_result)
    except Exception as e:
        _record_tool_call("llm", "timeout" if "timeout" in str(e).lower() else "error", round((time.perf_counter() - t0) * 1000), purpose="public_facility_summary")
        return _public_facility_fallback_text(user_message, poi_result)

def _independent_items(intent: str, city: str = "", keyword: str = "",
                       filters: dict = None, limit: int = 5) -> list:
    # ❌ 已禁用（debug_only）：这是"{城市}老城慢走/午餐备选区/夜景慢逛"等模板路线的源头之一。
    # 用户可见路线/餐饮只允许来自真实 amap POI 或 DeepSeek route_map_json，绝不用城市拼接模板兜底。
    return []
    # 禁止把用户原话当城市名：只用已知城市或"目的地"兜底
    raw_c = (city or "").replace("市", "").strip()
    c = raw_c if (_city_alias(raw_c) in CITY_GEO_INDEX or
                  any(raw_c in keys for keys in CITY_KEYWORDS.values())) else "目的地"
    if intent == "hotel_search":
        return []
    if intent in ("ticket_search", "group_buy_query"):
        city_routes = {
            "杭州": ["西湖湖边慢走", "灵隐寺外茶田散步", "河坊街傍晚慢逛"],
            "上海": ["外滩滨江慢走", "武康路梧桐街拍", "陆家嘴夜景收尾"],
            "北京": ["什刹海湖边慢走", "故宫角楼远眺", "鼓楼胡同夜色"],
            "厦门": ["环岛路海边散步", "鼓浪屿慢逛", "沙坡尾夜景收尾"],
            "承德": ["避暑山庄上午游览", "普宁寺文化参观", "双塔山傍晚收尾"],
            "桂林": ["象鼻山远眺", "东西巷慢逛", "两江四湖夜景"],
            "苏州": ["拙政园外园林慢走", "平江路老城慢逛", "七里山塘夜景"],
        }
        names = city_routes.get(c, [f"{c}老城慢走", f"{c}本地街巷散步", f"{c}夜景慢逛"])
        items = [
            {"name": names[0], "address": f"{c}市区", "rating": "", "cost": "", "distance": "按当天路线选择", "type": "景点/街区", "booking_status": "自行安排", "advantage": "需二次确认，不代表具体商户或门票商品。"},
            {"name": names[1], "address": f"{c}老城或主街附近", "rating": "", "cost": "", "distance": "按住宿位置调整", "type": "街区/文化", "booking_status": "自行安排", "advantage": "需二次确认，不代表具体商户或门票商品。"},
            {"name": names[2], "address": f"{c}适合晚间停留的位置", "rating": "", "cost": "", "distance": "晚间安排", "type": "夜景/收尾", "booking_status": "自行安排", "advantage": "需二次确认，不代表具体商户或门票商品。"},
        ]
    else:
        city_foods = {
            "杭州": ["湖滨附近午餐备选区", "河坊街小吃慢逛", "西湖边茶馆休息"],
            "上海": ["外滩附近午餐备选区", "老城厢本帮菜备选", "武康路咖啡休息"],
            "北京": ["鼓楼附近午餐备选区", "前门小吃慢逛", "什刹海边茶歇"],
            "厦门": ["中山路午餐备选区", "沙坡尾咖啡休息", "环岛路海鲜备选"],
            "承德": ["老街午餐备选区", "山庄附近茶歇", "夜市晚餐备选"],
            "桂林": ["东西巷午餐备选区", "正阳步行街小吃", "两江四湖夜宵备选"],
            "苏州": ["平江路午餐备选区", "观前街小吃慢逛", "山塘街晚餐备选"],
        }
        names = city_foods.get(c, [f"{c}午餐备选区", f"{c}本地小吃慢逛", f"{c}晚餐备选区"])
        items = [
            {"name": names[0], "address": f"{c}老城或主街附近", "rating": "", "cost": "", "distance": "顺路选择", "type": "午餐备选", "booking_status": "自行安排", "advantage": "需二次确认，不代表具体商户。"},
            {"name": names[1], "address": f"{c}居民区或老街附近", "rating": "", "cost": "", "distance": "靠近当天起点", "type": "小吃/茶歇", "booking_status": "自行安排", "advantage": "需二次确认，不代表具体商户。"},
            {"name": names[2], "address": f"{c}夜游路线附近", "rating": "", "cost": "", "distance": "晚间顺路", "type": "晚餐备选", "booking_status": "自行安排", "advantage": "需二次确认，不代表具体商户。"},
        ]
    return [dict(x, source="local_reference", is_real_meituan=False, is_area_suggestion=True,
                 data_level="C_MOCK_REGION", can_order=False) for x in items[:limit]]

def _is_real_meituan_item(item: dict) -> bool:
    return bool(isinstance(item, dict) and item.get("source") == "meituan_skill" and item.get("is_real_meituan"))

def _enrich_real_merchant_fields(items: list) -> list:
    """为美团真实商户补齐 is_real_merchant / can_order 等字段，供前端打「美团真实资源」标签与生成待确认订单。"""
    for it in items or []:
        if _is_real_meituan_item(it):
            it.setdefault("is_real_merchant", True)
            it.setdefault("can_order", True)
            it.setdefault("deal_available", True)
            it.setdefault("avg_price", it.get("cost", ""))
            it.setdefault("category", it.get("type", ""))
    return items

def _is_real_map_poi_item(item: dict) -> bool:
    return bool(isinstance(item, dict) and item.get("data_level") == "B_REAL_MAP_POI" and item.get("data_source") == "amap")

def _resource_data_tier(hotels: list, foods: list, sights: list) -> dict:
    real_hotels = [x for x in hotels if _is_real_meituan_item(x)]
    real_foods = [x for x in foods if _is_real_meituan_item(x)]
    real_sights = [x for x in sights if _is_real_meituan_item(x)]
    amap_count = len([x for x in [*hotels, *foods, *sights] if _is_real_map_poi_item(x)])
    real_count = len(real_hotels) + len(real_foods) + len(real_sights)
    area_count = len([x for x in [*hotels, *foods, *sights] if x.get("is_area_suggestion")])
    if real_hotels and real_foods and real_sights:
        tier = "A"
        label = "真实资源规划"
    elif real_count or amap_count:
        tier = "B"
        label = "半真实规划"
    else:
        tier = "C"
        label = "兜底规划"
    return {
        "tier": tier,
        "label": label,
        "use_real_results": bool(real_count),
        "use_fallback_template": not bool(real_count or amap_count),
        "real_counts": {"hotels": len(real_hotels), "foods": len(real_foods), "sights": len(real_sights)},
        "amap_poi_count": amap_count,
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
    ctx = user_context or {}
    user_id = _safe_user_id(ctx.get("user_id") or ctx.get("session_user_id") or "")
    session_id = str(ctx.get("session_id") or "default").strip() or "default"
    validation_tags = _order_validation_tags(item or {}, ctx)
    order = {
        "order_id": order_id,
        "user_id": user_id,
        "session_id": session_id,
        "status": "pending_confirm",
        "order_type": order_type or "unknown",
        "item": item or {},
        "user_context": {**ctx, "user_id": user_id, "session_id": session_id},
        "validation_tags": validation_tags,
        "created_at": now,
        "expire_in_minutes": 15,
        "action_required": "user_confirm",
        "message": "已生成待确认订单，等待用户确认。",
        "cta": {"type": "confirm_mock_order", "text": "确认预订"},
    }
    PENDING_ORDERS[order_id] = order
    _record_tool_call("mock_order", "ready", 0, order_type=order.get("order_type", ""))
    return {"success": True, "order": order}

ORDER_TYPE_LABELS = {
    "hotel": "酒店", "restaurant": "餐厅", "activity": "景点/活动",
    "ticket": "门票/景点", "groupbuy": "团购",
    "ride_hailing": "网约车", "flight_ticket": "机票", "train_ticket": "高铁",
}

def _build_booking_dispatch(order: dict) -> dict:
    """生成「商家 + 用户」双回执：确认后商家和用户同时收到该 Agent 预定。演示用。"""
    order = order or {}
    item = order.get("item", {}) or {}
    order_type = order.get("order_type", "") or "resource"
    type_label = ORDER_TYPE_LABELS.get(order_type) or item.get("category") or "资源"
    merchant = item.get("merchant") if isinstance(item.get("merchant"), dict) else {}
    operator_name = {
        "ride_hailing": "马到橙功网约车平台",
        "train_ticket": "12306 铁路服务",
    }.get(order_type, "")
    merchant_name = merchant.get("name") or operator_name or item.get("name") or f"{item.get('city','')}{type_label}商家"
    qty = item.get("quantity") or item.get("passengers") or 1
    voucher = "MV-" + uuid.uuid4().hex[:6].upper()
    dispatched_at = time.strftime("%H:%M:%S", time.localtime())
    merchant_receipt = {
        "channel": "merchant",
        "merchant_name": merchant_name,
        "category": type_label,
        "order_id": order.get("order_id", ""),
        "quantity": qty,
        "amount": item.get("price_estimate", ""),
        "address": item.get("address") or merchant.get("address", ""),
        "received_at": dispatched_at,
        "status": "已接单",
        "note": "Agent 预定已送达商家，商家已确认接单。",
    }
    user_receipt = {
        "channel": "user",
        "order_id": order.get("order_id", ""),
        "voucher_code": voucher,
        "amount": item.get("price_estimate", ""),
        "received_at": dispatched_at,
        "status": "预定成功",
        "note": "你的预定已生成凭证，凭码到店/上车核销。",
    }
    return {
        "dispatched_at": dispatched_at,
        "both_received": True,
        "summary": f"🍊 商家「{merchant_name}」与用户已同时收到该预定（{dispatched_at}）。",
        "merchant_receipt": merchant_receipt,
        "user_receipt": user_receipt,
    }

def tool_confirm_mock_order(order_id: str, user_id: str = "") -> dict:
    order = PENDING_ORDERS.get(order_id)
    if not order:
        return {"success": False, "error": "订单不存在或已过期"}
    expected_user_id = order.get("user_id") or "default_user"
    request_user_id = _safe_user_id(user_id or expected_user_id)
    if expected_user_id != "default_user" and request_user_id != expected_user_id:
        return {"success": False, "error": "订单不属于当前用户"}
    order["status"] = "mock_order_success"
    order["confirmed_at"] = int(time.time())
    dispatch = _build_booking_dispatch(order)
    order["dispatch"] = dispatch
    _record_tool_call("mock_order", "success", 0, order_id=order_id, order_type=order.get("order_type", ""))
    return {
        "success": True,
        "order_id": order_id,
        "status": "mock_order_success",
        "message": "🍊 模拟下单成功，已加入行程。" + dispatch["summary"],
        "dispatch": dispatch,
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

_TAXI_PLACEHOLDER_VALUES = {
    "当前位置/酒店", "当前位置", "当前城市", "当前位置城市", "本地",
    "目的地", "下一站", "目标地点", "出发地", "上海", "shanghai",
}

def _strip_taxi_coord_hints(text: str) -> str:
    s = str(text or "")
    s = re.sub(r"[\[（(][^\]）)]*(?:纬度|经度|lat|lng|longitude|当前位置)[^\]）)]*[\]）)]", "", s, flags=re.I)
    s = re.sub(r"\n+\[任务硬约束\].*$", "", s, flags=re.S)
    return s.strip()

def _taxi_clean_value(value) -> str:
    s = _strip_taxi_coord_hints(str(value or "")).strip()
    s = re.sub(r"^(?:帮我|给我|请|麻烦|我想|我要|想要|想)\s*", "", s)
    s = re.sub(r"^(?:打车|叫车|网约车|出租车|接驳)\s*(?:去|到|前往)?\s*", "", s)
    s = re.sub(r"^(?:去|到|前往)\s*", "", s)
    s = re.sub(r"(?:打车|叫车|网约车|出租车|接驳|下单|预订|预约|导航|路线|一下|吧|呀)$", "", s)
    s = re.sub(r"[，。！？、,.!?;；：:\s]+$", "", s)
    return s.strip(" -→")

def _taxi_is_placeholder(value, city_hint: str = "", allow_city: bool = False) -> bool:
    v = _taxi_clean_value(value)
    if not v:
        return True
    low = v.lower()
    if v in _TAXI_PLACEHOLDER_VALUES or low in _TAXI_PLACEHOLDER_VALUES:
        return True
    if re.search(r"^(?:最近(?:的)?|附近(?:的)?|就近|离我近|周边|热门景点|最近(?:的)?热门景点|景点|目的地|下一站|想去的地方)$", v):
        return True
    city_key = _city_alias(city_hint or "")
    if city_key and not allow_city and _city_alias(v) == city_key:
        return True
    return False

def _taxi_meaningful_value(value, city_hint: str = "", allow_city: bool = False) -> str:
    v = _taxi_clean_value(value)
    return "" if _taxi_is_placeholder(v, city_hint, allow_city) else v

def _taxi_extract_text_od(text: str, city_hint: str = "") -> dict:
    s = _strip_taxi_coord_hints(text)
    od = _extract_origin_destination(s, city_hint, "", "")
    origin = _taxi_meaningful_value(od.get("origin", ""), city_hint)
    destination = _taxi_meaningful_value(od.get("destination", ""), city_hint, allow_city=True)
    if not destination:
        patterns = (
            r"(?:打车|叫车|网约车|出租车|接驳)\s*(?:去|到|前往)\s*([^，。！？,;；\n]{2,30})",
            r"(?:去|到|前往)\s*([^，。！？,;；\n]{2,30})\s*(?:打车|叫车|网约车|出租车|接驳|$)",
        )
        for pat in patterns:
            m = re.search(pat, s)
            if m:
                destination = _taxi_meaningful_value(m.group(1), city_hint, allow_city=True)
                if destination:
                    break
    return {"origin": origin, "destination": destination}

def _taxi_first_route_point(value, city_hint: str = "") -> str:
    points = value or []
    if isinstance(points, str):
        points = [p.strip() for p in re.split(r"[>,，、|/]+", points) if p.strip()]
    if not isinstance(points, list):
        return ""
    for item in points:
        name = item.get("name") if isinstance(item, dict) else str(item or "")
        name = _taxi_meaningful_value(name, city_hint)
        if name:
            return name
    return ""

def _taxi_origin_label(coords: dict) -> str:
    if not coords:
        return ""
    return f"当前位置（纬度{float(coords['lat']):.6f},经度{float(coords['lng']):.6f}）"

def _taxi_generic_target(text: str) -> bool:
    return bool(re.search(r"最近|附近|就近|离我|周边|热门景点|下一站|景点|目的地|想去的地方", str(text or "")))

def _taxi_nearby_queries(text: str) -> list:
    s = str(text or "")
    if re.search(r"餐厅|吃饭|美食|饭店|咖啡|奶茶", s):
        return ["餐厅 美食", "咖啡店", "商场"]
    if re.search(r"酒店|住宿|民宿|宾馆", s):
        return ["酒店", "住宿"]
    if re.search(r"商场|购物|逛街", s):
        return ["商场 购物中心", "商业街"]
    if re.search(r"地铁|车站|机场|高铁|火车", s):
        return ["地铁站", "火车站", "机场"]
    return ["景点 景区 公园 博物馆 地标", "商场 购物中心", "公园"]

def _taxi_item_distance_m(item: dict, coords: dict) -> Optional[int]:
    loc = _extract_coord_pair(item) or _extract_coord_pair((item or {}).get("location"))
    if loc and coords:
        return int(round(_haversine(float(coords["lat"]), float(coords["lng"]), float(loc["lat"]), float(loc["lng"])) * 1000))
    raw = (item or {}).get("distance")
    try:
        if raw not in (None, "", []):
            return int(float(raw))
    except Exception:
        return None
    return None

def _taxi_support_type_allowed(text: str, item_type: str) -> bool:
    s = str(text or "")
    t = str(item_type or "")
    if re.search(r"餐厅|吃饭|美食|饭店|咖啡|奶茶", s):
        return t in {"餐厅", "咖啡店", "餐饮中心", "商场"}
    if re.search(r"酒店|住宿|民宿|宾馆", s):
        return False
    if re.search(r"商场|购物|逛街", s):
        return t in {"商场", "商业街", "便利店"}
    if re.search(r"地铁|车站|机场|高铁|火车", s):
        return t in {"地铁站/车站", "地铁站"}
    return t in {"景点服务区", "游客中心", "公园", "商场", "地铁站/车站", "图书馆", "社区中心"}

def _pick_nearby_taxi_target(coords: dict, city: str, text: str) -> dict:
    if not coords:
        return {}
    location = f"{float(coords['lng'])},{float(coords['lat'])}"
    seen = set()
    for radius in (1000, 3000, 5000):
        for query in _taxi_nearby_queries(text):
            rows = search_amap_place(query, city or "", 6, location=location, radius=radius) or []
            for item in rows:
                name = _taxi_meaningful_value(item.get("name"), city)
                if not name or name in seen:
                    continue
                dist_m = _taxi_item_distance_m(item, coords)
                if dist_m is None or dist_m > int(radius * 1.3):
                    continue
                seen.add(name)
                loc = _extract_coord_pair(item) or _extract_coord_pair(item.get("location"))
                return {
                    "name": name,
                    "address": item.get("address", ""),
                    "lat": loc.get("lat") if loc else item.get("lat"),
                    "lng": loc.get("lng") if loc else item.get("lng"),
                    "distance": dist_m,
                    "source": "map",
                    "radius": radius,
                }
        support_rows = search_nearby_toilet_support_osm(float(coords["lat"]), float(coords["lng"]), radius, 8, "all") or []
        for item in support_rows:
            if not _taxi_support_type_allowed(text, item.get("type", "")):
                continue
            name = _taxi_meaningful_value(item.get("name"), city)
            if not name or name in seen:
                continue
            dist_m = _taxi_item_distance_m(item, coords)
            if dist_m is None or dist_m > int(radius * 1.3):
                continue
            loc = _extract_coord_pair(item) or _extract_coord_pair(item.get("location"))
            return {
                "name": name,
                "address": item.get("address", ""),
                "lat": loc.get("lat") if loc else item.get("lat"),
                "lng": loc.get("lng") if loc else item.get("lng"),
                "distance": dist_m,
                "source": "map",
                "radius": radius,
            }
    return {}

def _resolve_mock_taxi_request(body: dict, city_hint: str = "", user_message: str = "") -> dict:
    b = body or {}
    text = user_message or b.get("user_query") or b.get("message") or b.get("trigger_reason") or ""
    coords = (
        _extract_coord_pair({"lat": b.get("lat"), "lng": b.get("lng")})
        or _extract_coord_pair({"lat": b.get("latitude"), "lng": b.get("longitude")})
        or _extract_coord_pair(b.get("userLocation"))
        or _extract_coord_pair(b.get("location"))
        or _extract_coord_pair(b.get("current_location"))
        or _parse_lat_lng(text)
    )
    text_od = _taxi_extract_text_od(text, city_hint)
    loc_city = _nearest_city_from_coords(float(coords["lat"]), float(coords["lng"]), "") if coords else ""
    explicit_city = _city_alias(text_od.get("destination", ""))
    explicit_city = explicit_city if explicit_city in CITY_GEO_INDEX else ""
    payload_city = _taxi_meaningful_value(b.get("city", ""), "", allow_city=True)
    city = explicit_city or loc_city or payload_city or _taxi_meaningful_value(city_hint, "", allow_city=True)

    origin = (
        _taxi_meaningful_value(b.get("from"), city)
        or _taxi_meaningful_value(b.get("origin"), city)
        or text_od.get("origin")
        or _taxi_origin_label(coords)
    )
    if not origin:
        return {
            "success": False,
            "error": "上车位置待确认，请开启定位或发送当前位置。",
        }

    payload_dest = (
        _taxi_meaningful_value(b.get("to"), city)
        or _taxi_meaningful_value(b.get("destination"), city)
        or _taxi_meaningful_value(b.get("target"), city)
    )
    route_dest = _taxi_first_route_point(b.get("route_points"), city)
    destination = payload_dest or text_od.get("destination") or route_dest
    destination_place = {}
    is_generic_destination = _taxi_generic_target(destination or text)
    if is_generic_destination and coords:
        destination_place = _pick_nearby_taxi_target(coords, city, destination or text)
        if destination_place.get("name"):
            destination = destination_place["name"]
        elif _taxi_generic_target(destination):
            destination = ""
    if not destination:
        return {
            "success": False,
            "error": "目的地待确认，可选择：路线下一站 / 手动填写目的地 / 重新生成路线卡。",
        }

    user_context = dict(b.get("user_context") or {})
    if coords:
        user_context["origin_location"] = {"lat": coords["lat"], "lng": coords["lng"]}
    if destination_place.get("lat") is not None and destination_place.get("lng") is not None:
        user_context["destination_location"] = {"lat": destination_place["lat"], "lng": destination_place["lng"]}
        user_context["destination_address"] = destination_place.get("address", "")
    return {
        "success": True,
        "origin": origin,
        "destination": destination,
        "city": city or loc_city or payload_city,
        "coords": coords,
        "destination_place": destination_place,
        "user_context": user_context,
    }

def tool_mock_request_ride(origin: str = "", destination: str = "",
                           city: str = "", trigger_reason: str = "",
                           user_context: dict = None) -> dict:
    """生成打车待确认订单。演示用，不调用真实网约车平台。"""
    ctx = user_context or {}
    origin = origin or ctx.get("origin") or ""
    destination = destination or ctx.get("destination") or ""
    if not origin or not destination:
        return {"success": False, "error": "上车位置或目的地待确认，暂不生成打车订单。"}
    seed = f"{city}|{origin}|{destination}|{trigger_reason}"
    origin_loc = _extract_coord_pair(ctx.get("origin_location"))
    dest_loc = _extract_coord_pair(ctx.get("destination_location"))
    if origin_loc and dest_loc:
        distance_km = round(_haversine(float(origin_loc["lat"]), float(origin_loc["lng"]), float(dest_loc["lat"]), float(dest_loc["lng"])), 1)
        eta = max(3, min(35, int(round(distance_km * 4 + 3))))
    else:
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

def tool_mock_book_train(origin: str = "", destination: str = "",
                         date: str = "", seat_class: str = "二等座",
                         passengers: int = 1, user_context: dict = None) -> dict:
    """生成高铁/火车票待确认订单。演示用，不真实出票；确认后商家与用户同时收到预定。"""
    ctx = user_context or {}
    origin = origin or ctx.get("origin") or "出发地"
    destination = destination or ctx.get("destination") or "目的地"
    passengers = max(1, int(passengers or ctx.get("passengers") or 1))
    seat_class = seat_class or "二等座"
    seed = f"{origin}|{destination}|{date}|{seat_class}"
    train_no = "G" + str(_mock_int(seed + "no", 100, 1999))
    times = [("07:12", "09:36"), ("10:05", "12:28"), ("14:40", "17:02"), ("18:55", "21:20")]
    dep, arr = times[_mock_int(seed + "slot", 0, len(times) - 1)]
    price_factor = {"商务座": 3.0, "一等座": 1.6, "二等座": 1.0}
    base = _mock_int(seed + "price", 120, 580)
    unit = round(base * price_factor.get(seat_class, 1.0))
    duration_h = round(_mock_int(seed + "dur", 12, 36) / 10, 1)
    left = _mock_int(seed + "left", 3, 60)
    train = {
        "provider": "马到橙功 Mock Rail",
        "train_no": train_no,
        "origin": origin,
        "destination": destination,
        "depart_time": dep,
        "arrive_time": arr,
        "duration": f"约{duration_h}小时",
        "seat_class": seat_class,
        "price": unit,
        "left_seats": left,
        "date": date,
    }
    item = {
        "name": f"{origin} → {destination} 高铁票",
        "city": destination,
        "origin": origin,
        "destination": destination,
        "category": "高铁",
        "price_estimate": unit * passengers,
        "passengers": passengers,
        "rating": "4.9",
        "train": train,
        "selected_items": [{
            "type": "train_ticket",
            "name": f"{train_no} {seat_class}",
            "price": f"{unit} × {passengers}",
            "rating": "4.9",
            "address": f"{origin} {dep} → {destination} {arr}",
        }],
        "recommend_reason": f"已按时间、席别和余票匹配高铁 {train_no}，等待确认后模拟出票。",
    }
    pending = tool_create_pending_order("train_ticket", item, {
        **ctx, "city": destination, "origin": origin, "destination": destination,
        "budget": _mock_budget_from_context(ctx, unit * passengers * 2),
        "passengers": passengers,
    })
    return {"success": True, "type": "train_options", "train": train, "order": pending["order"]}

RESOURCE_BOOKING_PRESET = {
    "hotel": {"label": "酒店", "type": "hotel",
              "names": ["亚朵S酒店", "全季酒店", "和颐至尚酒店", "丽呈华廷酒店"],
              "low": 220, "high": 880, "spot": ["市中心店", "核心商圈店", "地铁口店", "江景店"]},
    "ticket": {"label": "门票/景点", "type": "ticket",
               "names": ["地标观光票", "海洋公园门票", "欢乐谷一日票", "野生动物园门票"],
               "low": 40, "high": 320, "spot": ["景区正门", "官方旗舰店", "在线预约处", "线上售票处"]},
    "restaurant": {"label": "餐厅", "type": "restaurant",
                   "names": ["本帮菜馆", "蟹宴私房菜", "老字号酒楼", "海鲜酒家"],
                   "low": 80, "high": 460, "spot": ["旗舰店", "核心商圈店", "步行街店", "滨江店"]},
}

def _mock_resource_fallback(city: str, keyword: str = "", intent: str = "") -> list:
    """美团/高德都无结果时的 Mock 兜底资源（演示数据，非真实商户）。
    名称统一标注「Mock演示」，绝不伪造看起来真实的店名；并标记 is_real_merchant=False、can_order=False，
    前端据此显示「备用建议 / Mock演示」并禁止生成真实订单。"""
    city = city or "本地"
    kind = "hotel" if intent == "hotel_search" else "ticket" if intent == "ticket_search" else "restaurant"
    preset = RESOURCE_BOOKING_PRESET.get(kind, RESOURCE_BOOKING_PRESET["restaurant"])
    label = preset["label"]
    out = []
    for i in range(4):
        seed = f"{city}|{kind}|{keyword}|{i}"
        price = _mock_int(seed + "p", preset["low"], preset["high"])
        out.append({
            "name": f"{city}{label}·Mock演示{i + 1}",
            "cost": price, "price": price, "avg_price": price,
            "rating": str(round(4.3 + _mock_int(seed + "r", 0, 6) / 10, 1)),
            "address": f"{city}（示例位置，非真实商户）",
            "distance": "",
            "category": label,
            "tags": ["Mock演示", "非真实商户"],
            "deal_available": False,
            "source": "mock_fallback",
            "is_real_merchant": False,
            "can_order": False,
            "is_area_suggestion": True,
            "data_level": "C_MOCK_REGION",
        })
    return out

def tool_mock_book_resource(booking_kind: str = "hotel", city: str = "",
                            keyword: str = "", user_context: dict = None) -> dict:
    """生成酒店/门票景点/餐厅待确认订单（含商家数据）。确认后商家与用户同时收到预定。演示用。"""
    ctx = user_context or {}
    kind = booking_kind if booking_kind in RESOURCE_BOOKING_PRESET else "hotel"
    preset = RESOURCE_BOOKING_PRESET[kind]
    city = city or ctx.get("city") or "本地"
    seed = f"{city}|{kind}|{keyword}"
    base_name = keyword or preset["names"][_mock_int(seed + "name", 0, len(preset["names"]) - 1)]
    merchant_name = f"{base_name}（Mock演示）" if keyword else f"{city}{preset['label']}·Mock演示"
    spot = preset["spot"][_mock_int(seed + "spot", 0, len(preset["spot"]) - 1)]
    price = _mock_int(seed + "price", preset["low"], preset["high"])
    rating = round(4.3 + _mock_int(seed + "rate", 0, 6) / 10, 1)
    address = f"{city}{spot}"
    merchant = {"name": merchant_name, "address": address, "rating": str(rating), "price": price}
    item = {
        "name": merchant_name,
        "city": city,
        "category": preset["label"],
        "source": "mock_fallback",
        "is_real_merchant": False,
        "mock_notice": "Mock 演示数据，非真实商户，仅用于黑客松端到端演示。",
        "price_estimate": price,
        "rating": str(rating),
        "address": address,
        "merchant": merchant,
        "selected_items": [{
            "type": preset["type"], "name": merchant_name, "price": str(price),
            "rating": str(rating), "address": address,
        }],
        "recommend_reason": f"Mock 演示数据，非真实商户；已生成{preset['label']}待确认动作，等待确认后模拟下单。",
    }
    print("[MOCK_MARKED_AS_NON_REAL]")
    pending = tool_create_pending_order(preset["type"], item, {**ctx, "city": city})
    return {"success": True, "type": f"{kind}_booking", "booking_kind": kind,
            "merchant": merchant, "order": pending["order"]}

FLIGHT_AIRLINES = [("东方航空", "MU"), ("厦门航空", "MF"), ("中国国航", "CA"), ("春秋航空", "9C")]
FLIGHT_NOTE = "Mock 航班预订，仅用于黑客松端到端任务演示，不代表真实出票。"

def _flight_duration_label(dep: str, arr: str) -> str:
    def _to_min(t):
        h, m = str(t).split(":")
        return int(h) * 60 + int(m)
    diff = _to_min(arr) - _to_min(dep)
    if diff < 0:
        diff += 24 * 60
    h, m = divmod(diff, 60)
    return f"约{h}小时{m}分" if m else f"约{h}小时"

def tool_mock_search_flights(origin: str = "", destination: str = "",
                             date: str = "", budget: int = 0,
                             passengers: int = 1, cabin: str = "economy",
                             user_context: dict = None) -> dict:
    """本地 Mock 航班查询：返回模拟航班列表，不跳转任何外部网站。"""
    ctx = user_context or {}
    req = _extract_trip_requirements(f"{origin}到{destination}", origin or ctx.get("origin", "")) if not (origin and destination) else {}
    origin = origin or ctx.get("origin") or req.get("origin") or "出发地"
    destination = destination or ctx.get("destination") or req.get("destination") or "目的地"
    passengers = max(1, int(passengers or ctx.get("passengers") or 1))
    seed = f"{origin}|{destination}|{date}"
    times = [("06:40", "08:35"), ("09:30", "11:25"), ("13:15", "15:20"), ("18:50", "20:55")]
    flights = []
    for i, (dep, arr) in enumerate(times):
        airline, code = FLIGHT_AIRLINES[_mock_int(seed + "al" + str(i), 0, len(FLIGHT_AIRLINES) - 1)]
        flights.append({
            "flight_no": f"{code}-MOCK-{_mock_int(seed + 'no' + str(i), 1000, 9999)}",
            "origin": origin,
            "destination": destination,
            "depart_time": dep,
            "arrive_time": arr,
            "duration": _flight_duration_label(dep, arr),
            "price": _mock_int(seed + "p" + str(i), 680, 1680),
            "airline": airline,
            "status": "待确认",
        })
    recommended = flights[1] if len(flights) > 1 else flights[0]
    _record_tool_call("mock_flight", "ready", 0, origin=origin, destination=destination)
    return {
        "success": True,
        "type": "flight_mock",
        "origin": origin,
        "destination": destination,
        "date": date,
        "passengers": passengers,
        "flights": flights,
        "recommended": recommended,
        "note": FLIGHT_NOTE,
    }

def tool_mock_create_flight_order(flight: dict = None, user_context: dict = None) -> dict:
    """本地 Mock 机票下单：不跳转外部网站，直接返回 Mock 预订成功订单。"""
    flight = flight or {}
    order_id = "MDCG-FLIGHT-" + uuid.uuid4().hex[:8].upper()
    confirmed = dict(flight)
    confirmed["status"] = "mock_order_success"
    _record_tool_call("mock_flight", "success", 0, order_id=order_id, flight_no=flight.get("flight_no", ""))
    return {
        "success": True,
        "order_id": order_id,
        "status": "mock_order_success",
        "message": f"🍊 Mock 机票预订成功，订单号 {order_id}，已加入行程。",
        "flight": confirmed,
    }

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
    _record_tool_call("mock_monitor", "success", 0, city=city, resource_type=resource_type, target=target_name)
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

def _meituan_category_from_intent(intent: str = "", keyword: str = "") -> str:
    text = f"{intent} {keyword}"
    if re.search(r"hotel|酒店|住宿|宾馆|民宿", text, re.I):
        return "hotel"
    if re.search(r"ticket|门票|景点|活动", text, re.I):
        return "ticket"
    if re.search(r"group|团购|优惠|券", text, re.I):
        return "deal"
    return "restaurant"

def _normalize_meituan_append_item(item: dict) -> dict:
    item = item if isinstance(item, dict) else {}
    price = item.get("avg_price") or item.get("cost") or item.get("price") or ""
    return {
        "name": item.get("name") or "",
        "rating": item.get("rating") or "",
        "avg_price": price,
        "address": item.get("address") or item.get("area") or "",
        "area": item.get("area") or "",
        "distance": item.get("distance") or "",
        "tags": item.get("tags") if isinstance(item.get("tags"), list) else ([item.get("type")] if item.get("type") else []),
        "source": "meituan_real",
        "is_real_merchant": True,
        "need_verify": True,
        "can_order": False,
        "lat": item.get("lat"),
        "lng": item.get("lng"),
        "raw": {k: v for k, v in item.items() if k in ("type", "category", "deal_available", "data_level")},
    }

def _meituan_append_payload(success: bool, city: str, category: str, items: list = None,
                            message: str = "", keyword: str = "") -> dict:
    normalized = [_normalize_meituan_append_item(x) for x in (items or []) if isinstance(x, dict) and x.get("name")]
    if success and normalized:
        print(f"[MEITUAN_REAL_RESULTS_COUNT] {len(normalized)}")
        return {
            "type": "meituan_append",
            "reply_type": "meituan_real_append",
            "success": True,
            "city": city or "",
            "category": category or "restaurant",
            "keyword": keyword or "",
            "count": len(normalized),
            "items": normalized[:6],
            "results": normalized[:6],
            "actions": [
                {"label": "替换进路线", "action_type": "replace_route_with_meituan_item", "payload": {}},
                {"label": "生成 Mock 取号/预订", "action_type": "restaurant_confirm", "payload": {}},
                {"label": "查看地图路线", "action_type": "open_amap_route", "payload": {}},
                {"label": "换一家", "action_type": "replace_restaurant", "payload": {}},
            ],
            "message": message or "已补充美团真实资源",
        }
    print("[MEITUAN_REAL_RESULTS_COUNT] 0")
    print("[MOCK_FALLBACK_USED] meituan_real_unavailable")
    print("[MOCK_MARKED_AS_NON_REAL]")
    return {
        "type": "meituan_append",
        "reply_type": "meituan_real_append",
        "success": False,
        "city": city or "",
        "category": category or "restaurant",
        "keyword": keyword or "",
        "items": [],
        "results": [],
        "message": message or MEITUAN_REAL_FRIENDLY_FALLBACK,
        "mock_notice": "Mock 演示数据，非真实商户，仅用于黑客松端到端演示。",
    }

def _meituan_cli_query(intent: str, city: str, keyword: str, filters: dict) -> str:
    filters = filters or {}
    parts = []
    if intent == "hotel_search":
        parts.append(f"{city}酒店推荐 真实酒店 店名 评分 价格")
    elif intent == "ticket_search":
        parts.append(f"{city}景点门票推荐 真实景点 店名 评分 价格")
    elif intent == "group_buy_query":
        parts.append(f"{city}餐饮团购优惠推荐 真实店名 评分 人均价格")
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

    # ── 方法1：mttravel 自然语言格式 ──
    # 关键判据：真实店名总是 **加粗** 且紧跟一个空行(段落分隔)；而 **4.8的高分** / **团购优惠**
    # 这类描述性加粗后面跟的是标点或文字，不是空行。据此把店名从描述性加粗里精确切出来，
    # 同时能抓到 mttravel 把下一家店名粘在上一段末尾(…准没错啦！**XX店**\n\n)的情况。
    # 店名总是「行尾加粗」：**店名** 后面紧跟换行；而 **4.8的高分**/**团购优惠** 这类描述性加粗
    # 后面跟的是标点或文字(行内)，据此区分。兼容 **店名**\n\n 与 **店名**\n 两种 mttravel 输出。
    name_span_re = re.compile(r'\*\*([^*\n]{2,60})\*\*[ \t]*\r?\n')
    skip_words = r'小贴士|贴士|温馨提示|注意事项|总结|以下|更多|筛选|如果你|小团'
    matches = list(name_span_re.finditer(s))
    seen_names: set[str] = set()
    for mi, m in enumerate(matches):
        if len(items) >= limit:
            break
        name = re.sub(r'[*_`\\]', '', m.group(1)).strip()
        if not name or len(name) < 2 or len(name) > 60:
            continue
        if re.search(skip_words, name) or re.fullmatch(r'[\d.\s分元¥￥%、，,]+', name):
            continue
        # 兜底过滤极少数仍后接空行的纯描述性加粗
        if re.fullmatch(r'(?:团购优惠|优惠|评分|高分|超高评分|人均价?格?|海景|招牌|特色|推荐|性价比|环境|氛围)', name):
            continue
        if name in seen_names:
            continue
        seen_names.add(name)
        # 描述只取到下一家店名之前，避免把别家的评分/人均串到这一家
        desc_end = matches[mi + 1].start() if mi + 1 < len(matches) else len(s)
        desc = s[m.end(): min(desc_end, m.end() + 320)].strip()
        # 评分写法多样：4.8分 / 4.8的高分 / 评分高达4.8分 / 4.9分的超高评分
        rating_m = (re.search(r'(\d\.\d)(?=\s*[的高超棒满分]{0,4}分)', desc)
                    or re.search(r'(?:评分|高达)[^0-9]{0,4}(\d\.\d)', desc))
        rating = rating_m.group(1) if rating_m else ""
        price_m = (re.search(r'人均[约为]?\s*[¥￥]?\s*(\d{2,4})', desc)
                   or re.search(r'([¥￥]\d[\d.,xX]*)', desc))
        price = price_m.group(1) if price_m else ""
        addr_m = re.search(r'📍\s*([^\n]+)', desc) or re.search(r'地址[：:]\s*([^\n。，]+)', desc)
        addr = addr_m.group(1).strip() if addr_m else ""
        items.append({
            "name": name,
            "address": addr,
            "rating": rating,
            "cost": price,
            "distance": "",
            "type": _sec_at(m.start()),
            "deal_available": bool(re.search(r'团购|优惠|代金券|套餐|团单|特团', desc)),
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

def _budget_breakdown(total_budget: int, days: int, distance_km: float, wants_hotel: bool = False) -> dict:
    days = max(1, int(days or 1))
    nights = max(1, days - 1)
    strategy = _budget_strategy(total_budget)
    # #13：1 日游默认不含住宿预算；仅 days>=2 或用户明确要订酒店/过夜时才计入
    include_hotel = days > 1 or bool(wants_hotel)
    if not include_hotel and total_budget <= 500:
        transport = round(total_budget * 0.16)
        food = round(total_budget * 0.36)
        tickets = round(total_budget * 0.24)
        local = round(total_budget * 0.12)
        hotel = 0
    else:
        transport = min(round(total_budget * (0.10 if total_budget <= 500 else 0.13)), 320)
        if distance_km > 500:
            transport = max(transport, min(round(total_budget * 0.28), 900))
        elif distance_km >= 50:
            transport = max(transport, 180)
        if include_hotel:
            hotel = round(total_budget * (0.36 if days > 1 else 0.24))
            food = round(total_budget * (0.20 if total_budget <= 500 else 0.22))
            tickets = round(total_budget * (0.16 if total_budget <= 500 else 0.20))
            local = round(total_budget * 0.06)
        else:
            # 把住宿份额分摊到餐饮/门票/本地，1 日游更贴实际
            hotel = 0
            food = round(total_budget * (0.36 if total_budget <= 500 else 0.32))
            tickets = round(total_budget * (0.24 if total_budget <= 500 else 0.30))
            local = round(total_budget * (0.12 if total_budget <= 500 else 0.10))
    used = hotel + transport + food + tickets + local
    buffer = total_budget - used
    if buffer < 0:
        tickets = max(0, tickets + buffer)
        buffer = 0
    return {
        "total": total_budget,
        "hotel": hotel,
        "hotel_nightly_cap": max(180, round(hotel / nights)) if hotel else 0,
        "transport": transport,
        "food": food,
        "tickets": tickets,
        "local": local,
        "snacks": local,
        "buffer": buffer,
        "nights": nights,
        "strategy": strategy,
        "status": "接近上限" if buffer <= max(30, round(total_budget * 0.1)) else "未超支",
    }

def _budget_strategy(total_budget: int) -> str:
    total_budget = int(total_budget or 0)
    if total_budget <= 500:
        return "平价优先"
    if total_budget <= 1500:
        return "均衡"
    if total_budget <= 3000:
        return "舒适"
    return "高端"

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
    out["snacks"] = out.get("local", 0)
    out["strategy"] = _budget_strategy(total)
    out["status"] = "超预算" if used > total else ("接近上限" if out["buffer"] <= max(30, round(total * 0.1)) else "未超支")
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

    def natural_relax_food() -> str:
        return {
            "北京": "鼓楼附近午餐备选区",
            "杭州": "湖滨附近午餐备选区",
            "上海": "外滩附近午餐备选区",
            "厦门": "中山路午餐备选区",
            "苏州": "观前街午餐备选区",
            "桂林": "东西巷午餐备选区",
            "北海": "老街午餐备选区",
            "承德": "老街午餐备选区",
            "深圳": "南山附近午餐备选区",
            "新加坡": "牛车水午餐备选区",
        }.get(c, f"{c}午餐备选区")

    def natural_relax_evening() -> str:
        return {
            "北京": "什刹海傍晚慢走",
            "杭州": "湖滨夜景收尾",
            "上海": "外滩夜景收尾",
            "厦门": "环岛路傍晚慢走",
            "苏州": "平江路夜色收尾",
            "桂林": "两江四湖夜景收尾",
            "北海": "银滩傍晚收尾",
            "承德": "双塔山傍晚收尾",
            "深圳": "深圳湾夜景收尾",
            "新加坡": "滨海湾夜景收尾",
        }.get(c, f"{c}傍晚慢走")

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
        if len(route) >= 3:
            route = route[:3]
        elif len(route) >= 2:
            route = route + [food_name or natural_relax_food(), natural_relax_evening()]
        else:
            route = route + [food_name or natural_relax_food(), natural_relax_evening()]
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
    # ❌ 已禁用（debug_only）：这是每日行程卡的人格模板源头（老城慢走/午餐备选区/日落机位/审美咖啡店）。
    # 每日行程卡只允许由 _days_from_route_map() 从真实 route_map 派生；此函数不再进入用户可见结果。
    return []
    c = city.replace("市", "")
    real_sights = [x for x in sights if _is_real_meituan_item(x)]
    real_foods = [x for x in foods if _is_real_meituan_item(x)]
    area_sights = [x for x in sights if x.get("is_area_suggestion")]
    area_foods = [x for x in foods if x.get("is_area_suggestion")]

    def pick(items, idx, fallback):
        if not items:
            return fallback
        return items[idx % len(items)].get("name") or fallback

    def natural_sight(idx: int) -> str:
        defaults = {
            "承德": ["避暑山庄上午游览", "普宁寺文化参观", "双塔山傍晚收尾"],
            "北京": ["什刹海湖边慢走", "烟袋斜街胡同拍照", "鼓楼夜色收尾"],
            "杭州": ["西湖湖边慢走", "河坊街傍晚慢逛", "湖滨夜景收尾"],
            "厦门": ["沙坡尾艺术西区", "环岛路海边散步", "曾厝垵夜市收尾"],
            "桂林": ["象鼻山远眺", "东西巷慢逛", "两江四湖夜景"],
        }
        return defaults.get(c, [f"{c}老城慢走", f"{c}本地街巷散步", f"{c}夜景慢逛"])[idx % 3]

    def natural_food(idx: int) -> str:
        defaults = {
            "承德": ["老街午餐备选区", "山庄附近茶歇", "夜市晚餐备选"],
            "北京": ["鼓楼附近午餐备选区", "胡同咖啡休息", "前门小吃备选"],
            "杭州": ["湖滨附近午餐备选区", "西湖边茶馆休息", "河坊街小吃慢逛"],
            "厦门": ["中山路午餐备选区", "沙坡尾咖啡休息", "环岛路海鲜备选"],
            "桂林": ["东西巷午餐备选区", "正阳步行街小吃", "两江四湖夜宵备选"],
        }
        return defaults.get(c, [f"{c}午餐备选区", f"{c}茶歇休息", f"{c}晚餐备选区"])[idx % 3]

    if real_sights or real_foods:
        base = [
            {
                "theme": "真实资源开场",
                "route": [
                    f"{c}交通枢纽/酒店",
                    pick(real_sights or area_sights, 0, natural_sight(0)),
                    pick(real_foods or area_foods, 0, natural_food(0)),
                    pick(real_sights or area_sights, 1, natural_sight(2)),
                ],
                "transport": transport_mode,
                "tip": "优先使用工具返回的真实商户/景点，非真实点仅作为需二次确认的备选。",
            },
            {
                "theme": "真实餐饮与街区",
                "route": [
                    pick(real_sights or area_sights, 1, natural_sight(1)),
                    pick(real_foods or area_foods, 1, natural_food(1)),
                    pick(real_sights or area_sights, 2, natural_sight(2)),
                ],
                "transport": "地铁/打车 + 步行",
                "tip": "餐饮和活动按评分、价格、距离与状态权重排序。",
            },
            {
                "theme": "轻松返程",
                "route": [
                    pick(real_sights or area_sights, 2, natural_sight(2)),
                    pick(real_foods or area_foods, 2, natural_food(2)),
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
            {"theme":"老城慢走开场","route":[f"{c}交通枢纽/酒店", pick(area_sights, 0, natural_sight(0)), pick(area_foods, 0, natural_food(0))],"transport":transport_mode,"tip":"工具未返回真实商户时，仅生成需二次确认的自然路线节点。"},
            {"theme":"街巷与晚间收尾","route":[pick(area_sights, 1, natural_sight(1)), pick(area_foods, 1, natural_food(1)), natural_sight(2)],"transport":"地铁/打车 + 步行","tip":"非真实商户不生成订单，现场可用地图二次筛选。"},
            {"theme":"轻松返程","route":[pick(area_sights, 2, natural_sight(2)), natural_food(2), "返程"],"transport":"公共交通 + 枢纽接驳","tip":"返程日保留机动时间。"},
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
        food_name = food.get("name", natural_food(i))
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
            "food_note": "真实商户" if _is_real_meituan_item(food) else "需二次确认，不代表具体商户",
            "transport": tpl["transport"],
            "budget": day_ticket + day_food + day_local + (round((budget.get("transport", 0) or 0) / 2) if i in (0, days - 1) else 0),
            "tip": tpl["tip"],
            "rain_note": rain_note,
        })
    return out

_DAY_FOOD_KW = re.compile(r"餐|食|吃|小吃|菜|火锅|烧烤|海鲜|咖啡|茶馆|面|饭|宵")
_DAY_TYPE_ICON = {"餐厅": "food", "餐饮": "food", "美食": "food", "小吃": "food",
                  "景点": "sight", "景区": "sight", "公园": "sight", "商圈": "sight",
                  "酒店": "rest", "住宿": "rest", "夜景": "relax", "休息": "rest"}

def _days_from_route_map(route_map: list, budget: dict, days_count: int) -> list:
    """从真实 route_map（DeepSeek 基于真实地图 POI 生成）派生每日行程卡。
    彻底不使用任何模板/城市常识兜底：route_map 空则返回空，绝不编造节点。"""
    if not route_map:
        return []

    def _sch_type(t: str) -> str:
        s = str(t or "")
        for k, v in _DAY_TYPE_ICON.items():
            if k in s:
                return v
        return "sight"

    def _as_int(v) -> int:
        try:
            return int(float(v))
        except (TypeError, ValueError):
            return 0

    by_day: dict = {}
    for n in route_map:
        by_day.setdefault(int(n.get("day") or 1), []).append(n)
    out = []
    for d in sorted(by_day):
        nodes = [n for n in by_day[d] if str(n.get("name") or "").strip()]
        if not nodes:
            continue
        route = [str(n.get("name")).strip() for n in nodes]
        food_node = next((n for n in nodes
                          if _sch_type(n.get("type")) == "food" or _DAY_FOOD_KW.search(str(n.get("name") or ""))), {})
        transports = []
        for n in nodes:
            tr = str(n.get("next_transport") or "").strip()
            if tr and tr not in transports:
                transports.append(tr)
        schedule = [{
            "time": n.get("arrival_time") or n.get("time") or "",
            "type": _sch_type(n.get("type")),
            "activity": str(n.get("name")).strip(),
            "duration_min": _as_int(n.get("stay_minutes")),
        } for n in nodes]
        day_cost = sum(_as_int(n.get("estimated_cost")) for n in nodes)
        out.append({
            "day": d,
            "theme": "真实地点路线",
            "route": route,
            "schedule": schedule,
            "food": food_node.get("name", ""),
            "food_cost": food_node.get("estimated_cost", ""),
            "food_source": food_node.get("data_source", "amap"),
            "food_is_real_meituan": bool(food_node.get("is_real_poi")),
            "food_note": "地图可查到的真实地点" if food_node else "",
            "transport": " / ".join(transports) or "步行/打车",
            "budget": day_cost or round((budget.get("total", 0) or 0) / max(1, days_count)),
            "tip": "路线节点均来自地图真实 POI，可直接导航。",
            "rain_note": "",
        })
    return out

def _route_card_from_trip(origin: dict, dest: dict, req: dict, days: list,
                          budget: dict, persona_state: dict, decision: dict,
                          primary_transport: str, resource_quality: dict = None,
                          resources: list = None) -> dict:
    city = dest.get("name") or req.get("destination") or "目的地"
    labels = [str(x).replace("状态", "") for x in (persona_state.get("labels") or [])]
    persona_label = labels[0] if labels else "松弛感"
    day = days[0] if days else {}
    route = [x for x in (day.get("route") or []) if x]
    if not route:
        route = ["集合/出发点"]
    route = route[:5]
    if route and ("交通枢纽" in route[0] or "酒店" in route[0]):
        route[0] = "集合/出发点"
    if route and route[0] == city:
        route[0] = "集合/出发点"
    if not route or route[0] != "集合/出发点":
        route = ["集合/出发点"] + route
    natural_defaults = {
        "承德": ["避暑山庄上午游览", "老街午餐备选区", "普宁寺文化参观", "双塔山傍晚收尾"],
        "北京": ["什刹海湖边慢走", "鼓楼附近午餐备选区", "烟袋斜街胡同拍照", "鼓楼夜色收尾"],
        "杭州": ["西湖湖边慢走", "湖滨附近午餐备选区", "河坊街傍晚慢逛", "湖滨夜景收尾"],
        "厦门": ["中山路午餐备选区", "沙坡尾艺术西区", "环岛路海边散步", "曾厝垵夜市收尾"],
        "桂林": ["象鼻山远眺", "东西巷午餐备选区", "两江四湖夜景"],
    }.get(city, [f"{city}老城慢走", f"{city}午餐备选区", f"{city}本地街巷散步", f"{city}夜景慢逛"])
    banned = re.compile(r"区域建议开场|代表性景区区域|核心商圈餐饮区域|景点区域建议|餐饮区域建议|文化街区区域|小吃区域建议|夜游区域|夜景区域|低强度游览区域|伴手礼/早餐区域|景点·|餐饮·")
    cleaned_route = []
    for idx, name in enumerate(route):
        name = re.sub(r"^(?:景点|餐饮)[·:：]\s*", "", str(name or "").strip())
        if idx > 0 and (not name or banned.search(name)):
            name = natural_defaults[(idx - 1) % len(natural_defaults)]
        cleaned_route.append(name or natural_defaults[idx % len(natural_defaults)])
    route = cleaned_route
    while len(route) < 4:
        route.append(natural_defaults[(len(route) - 1) % len(natural_defaults)])
    real_counts = (resource_quality or {}).get("real_counts") or {}
    has_real_resource = bool((resource_quality or {}).get("use_real_results") or sum(real_counts.values() or [0]))
    resource_by_name = {}
    for item in resources or []:
        if item.get("name"):
            resource_by_name[item["name"]] = item
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
        if re.search(r"夜景|夜游|傍晚|落日|日落", name):
            return "夜景"
        if re.search(r"沙滩|海|湖|环岛|慢行|山庄|寺|街|胡同|园|山|博物馆", name):
            return "景点"
        return "景点"

    def _source_meta(name: str) -> tuple[str, bool, bool, bool]:
        item = resource_by_name.get(name) or {}
        if _is_real_meituan_item(item):
            return "meituan_skill", True, True, False
        if item.get("lat") and item.get("lng") and not item.get("is_area_suggestion"):
            return item.get("source") or "gaode_poi", True, False, False
        return "area_suggestion", False, False, True

    def _time_for(idx: int, typ: str, cur_min: int) -> int:
        if idx == 0:
            return cur_min
        if typ == "餐饮" and cur_min < 11 * 60 + 30:
            return 11 * 60 + 30
        if typ == "夜景" and cur_min < 17 * 60 + 30:
            return 17 * 60 + 30
        return cur_min

    start_min = 8 * 60 + 30 if "special_force" in (persona_state.get("keys") or []) else 9 * 60 + 30
    if "relax" in (persona_state.get("keys") or []) or "elder" in (persona_state.get("keys") or []):
        start_min = 10 * 60
    route_map = []
    cur_min = start_min
    for idx, name in enumerate(route):
        nxt = transport_plan[idx] if idx < len(transport_plan) else ("", 0)
        typ = _step_type(name, idx)
        cur_min = _time_for(idx, typ, cur_min)
        source, is_real, can_order, need_verify = _source_meta(name)
        stay = 0 if idx == 0 else (75 if typ == "餐饮" else 90 if typ == "景点" else 70)
        cost = 0 if idx == 0 else (round((budget.get("food", 0) or 0) / max(1, req.get("days", 1)) / 2) if typ == "餐饮" else round((budget.get("tickets", 0) or 0) / max(1, req.get("days", 1)) / 2))
        risk = "需二次确认，不生成订单" if need_verify else ("饭点可能排队，超过20分钟切换备选" if typ == "餐饮" else "热门时段注意排队")
        route_map.append({
            "step": idx + 1,
            "name": name,
            "type": typ,
            "time": f"{cur_min // 60:02d}:{cur_min % 60:02d}",
            "stay_minutes": stay,
            "short_desc": "按当前位置/集合点出发" if idx == 0 else "",
            "reason": "作为集合点锁定路线起点" if idx == 0 else ("真实工具结果，按评分/预算/位置进入路线" if is_real else "自然路线节点，需到店前二次确认"),
            "next_transport": nxt[0],
            "next_duration_minutes": nxt[1],
            "estimated_cost": cost,
            "data_source": source,
            "is_real_poi": is_real,
            "can_order": can_order,
            "need_verify": need_verify,
            "risk": risk,
        })
        cur_min += stay + (nxt[1] or 0)
    total_minutes = sum(x.get("stay_minutes", 0) for x in route_map) + sum(x[1] for x in transport_plan)
    if total_minutes < 300:
        total_minutes = 420 if req.get("days", 1) == 1 else total_minutes
    intensity = "高" if "special_force" in (persona_state.get("keys") or []) else ("低" if "elder" in (persona_state.get("keys") or []) else "中低")
    confidence = "真实资源优先" if has_real_resource else "需二次确认"
    timeline = []
    for item in route_map:
        timeline.append({"time": item["time"], "title": item["name"], "detail": item.get("reason", item["type"]), "cost": item.get("estimated_cost", 0), "risk": item.get("risk", "")})
    actions = [
        {"label": "更省钱", "action_type": "refine_budget"},
        {"label": "更松弛", "action_type": "refine_relax"},
        {"label": "特种兵", "action_type": "refine_special_force"},
        {"label": "避开排队", "action_type": "avoid_queue"},
        {"label": "加酒店", "action_type": "add_hotel", "requires_confirm": False},
    ]
    return {
        "answer_type": "trip_plan",
        "title": f"{city}{req.get('days', 1)}日行程规划",
        "city": city,
        "summary": f"🍊 {city} {req.get('days', 1)} 日{persona_label}路线",
        "route_map": route_map,
        "metrics": {
            "total_duration_minutes": total_minutes,
            "total_budget": budget.get("total"),
            "budget_per_person": budget.get("total"),
            "budget_range": f"约 ¥{max(200, round((budget.get('total') or 800) * 0.6))}-{budget.get('total') or 800}",
            "route_intensity": intensity,
            "walking_intensity": intensity,
            "queue_risk": "热门点排队，中午错峰",
            "data_confidence": confidence,
        },
        "budget": {
            "transport": budget.get("transport", 0),
            "food": budget.get("food", 0),
            "activity": budget.get("tickets", 0),
            "tickets": budget.get("tickets", 0),
            "hotel": budget.get("hotel", 0),
            "snacks": budget.get("snacks", budget.get("local", 0)),
            "local": budget.get("local", 0),
            "buffer": budget.get("buffer", 0),
            "strategy": budget.get("strategy", _budget_strategy(budget.get("total", 0))),
            "status": budget.get("status", "未超支"),
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
    plan_started = time.perf_counter()
    req = _extract_trip_requirements(user_prompt, city)
    route_waypoints = _extract_route_waypoints(user_prompt, city, req.get("origin", ""), req.get("destination", ""))
    waypoint_city = _route_city_from_waypoints(route_waypoints)
    if waypoint_city and _city_alias(req.get("destination", "")) not in CITY_GEO_INDEX:
        req["destination"] = waypoint_city
        req["city"] = waypoint_city
    soul_memory = req.get("soul_memory", {})
    soul_prefs = soul_memory.get("preferences", {}) or {}
    soul_food = soul_prefs.get("food", {}) if isinstance(soul_prefs, dict) else {}
    pstate = _persona_state(persona, user_prompt)
    origin = _resolve_place_info(req["origin"], city)
    dest = _resolve_place_info(req["destination"], city)
    city_name = _guard_city_name(dest.get("name") or req.get("destination") or city or "目的地")
    search_city_label = _city_search_label(city_name)
    print(f"[DESTINATION_DETECTED] raw={req.get('destination')} resolved={dest.get('name')} user_input={str(user_prompt or '')[:80]}")
    print(f"[FINAL_CITY_USED] {city_name}")
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
    amap_route = {}
    budget = _adjust_budget_by_persona(_budget_breakdown(req["budget"], req["days"], distance_km, req.get("wants_hotel")), pstate)
    proactive = _proactive_butler_defaults(req, decision, pstate, user_prompt, dest.get("name", ""))
    intent_card = _build_intent_understanding_card(req, pstate, decision, user_prompt)
    hotel_filter = {"price_high": budget["hotel_nightly_cap"], "rating": 4.5}
    if req["budget"] <= 500:
        food_keyword = "平价小吃 本地菜 免费景点"
    elif req["budget"] > 3000 or re.search(r"米其林|黑珍珠|高端|fine dining|纪念日", user_prompt, re.I):
        food_keyword = "米其林 黑珍珠 特色餐厅 高品质酒店"
    else:
        food_keyword = "本地菜 小吃 不辣" if soul_food.get("avoid_spicy") else "本地菜 小吃"
    food_search_keyword = f"{search_city_label} {food_keyword}".strip()
    sight_search_keyword = f"{search_city_label} 景点".strip()
    hotel_search_keyword = f"{search_city_label} 酒店".strip()
    print(f"[CANDIDATE_SEARCH_QUERY] city={city_name} food={food_search_keyword} sight={sight_search_keyword} hotel={hotel_search_keyword}")
    food_filter = {
        "price_high": max(40, round(budget["food"] / max(1, req["days"]))),
        "avoid_spicy": bool(soul_food.get("avoid_spicy")),
    }
    independent = req["planner_mode"] == "independent_trip"
    futures = {}
    results = {}
    if independent:
        # 普通出游规划默认走「快速规划链路」：不阻塞等待慢速美团真实资源（mttravel 实测 18-25s），
        # 仅在用户明确表达美团团购/订酒店/优惠/真实商户等意图时才调用美团真实资源。
        can_use_meituan_resources = bool(req.get("wants_meituan") or req.get("requires_real_meituan")) and not req.get("user_preference", {}).get("avoid_meituan")
        with ThreadPoolExecutor(max_workers=6 if can_use_meituan_resources else 4) as pool:
            if can_use_meituan_resources:
                futures["longcat_resources"] = pool.submit(tool_call_longcat_resource_search, dest.get("name",""), user_prompt, ["restaurant", "sight", "hotel", "groupbuy"], 8)
            futures["weather"] = pool.submit(_weather_aux, dest.get("name") or req["destination"])
            futures["amap_foods"] = pool.submit(search_amap_place, food_search_keyword, city_name, 6)
            futures["amap_sights"] = pool.submit(search_amap_place, sight_search_keyword, city_name, 6)
            if can_use_meituan_resources:
                futures["foods"] = pool.submit(tool_call_meituan_skill, "restaurant_search", city_name, food_search_keyword, "", None, None, food_filter, 6)
                futures["sights"] = pool.submit(tool_call_meituan_skill, "ticket_search", city_name, sight_search_keyword, "", None, None, {"price_high": max(80, round(budget["tickets"] / max(1, req["days"])))}, 6)
            try:
                results["weather"] = futures["weather"].result(timeout=REQUEST_TIMEOUT + 1)
            except Exception as e:
                _external_circuit_record("weather", False, _safe_error_text(e))
                results["weather"] = {"success": False, "error": WEATHER_FRIENDLY_FALLBACK, "message": WEATHER_FRIENDLY_FALLBACK}
            if can_use_meituan_resources:
                for key in ("foods", "sights"):
                    try:
                        results[key] = futures[key].result(timeout=MEITUAN_SKILL_TIMEOUT)
                    except Exception as e:
                        _external_circuit_record("meituan", False, _safe_error_text(e))
                        results[key] = {"success": False, "error": MEITUAN_REAL_FRIENDLY_FALLBACK, "message": MEITUAN_REAL_FRIENDLY_FALLBACK, "mock_notice": "Mock 演示数据，非真实商户，仅用于黑客松端到端演示。"}
            if "longcat_resources" in futures:
                try:
                    results["longcat_resources"] = futures["longcat_resources"].result(timeout=LONGCAT_RESOURCE_TIMEOUT + 1)
                except Exception as e:
                    _external_circuit_record("meituan", False, _safe_error_text(e))
                    results["longcat_resources"] = {"success": False, "message": MEITUAN_REAL_FRIENDLY_FALLBACK, "error": MEITUAN_REAL_FRIENDLY_FALLBACK, "mock_notice": "Mock 演示数据，非真实商户，仅用于黑客松端到端演示。"}
            else:
                results["longcat_resources"] = (
                    {"success": False, "message": "用户要求避开美团，未调用美团龙猫", "status": "blocked"}
                    if req.get("user_preference", {}).get("avoid_meituan")
                    else {"success": False, "message": "普通出游规划未触发美团真实资源，已用快速规划链路", "status": "skipped"}
                )
            for key in ("amap_foods", "amap_sights"):
                try:
                    results[key] = futures[key].result(timeout=REQUEST_TIMEOUT + 1)
                except Exception as e:
                    _external_circuit_record("map_search", False, _safe_error_text(e))
                    results[key] = []
        hotels = []
        foods = _attach_item_coords(_real_meituan_items(results.get("foods", {}), 6), city_name, allow_geocode=False) if can_use_meituan_resources else []
        sights = _attach_item_coords(_real_meituan_items(results.get("sights", {}), 6), city_name, allow_geocode=False) if can_use_meituan_resources else []
        if not foods:
            # 只用高德真实 POI，不再用 _independent_items 区域模板兜底；没有就为空
            foods = _attach_item_coords(results.get("amap_foods") or [], city_name, allow_geocode=False)
        if not sights:
            sights = _attach_item_coords(results.get("amap_sights") or [], city_name, allow_geocode=False)
    else:
        # commerce(明确美团意图)：主流程不阻塞等待慢速美团(mttravel ~18s)，路线用高德真实 POI 快速出图；
        # 美团真实商户由 wrapper(_rule_meituan_trip_agent_response) 后台搜索并追加，前端 3s 内先出方案。
        with ThreadPoolExecutor(max_workers=6) as pool:
            futures["longcat_resources"] = pool.submit(tool_call_longcat_resource_search, dest.get("name",""), user_prompt, ["hotel", "restaurant", "sight", "groupbuy"], 8)
            futures["weather"] = pool.submit(_weather_aux, dest.get("name") or req["destination"])
            futures["amap_hotels"] = pool.submit(search_amap_place, hotel_search_keyword, city_name, 3)
            futures["amap_foods"] = pool.submit(search_amap_place, food_search_keyword, city_name, 6)
            futures["amap_sights"] = pool.submit(search_amap_place, sight_search_keyword, city_name, 6)
            for key, fut in futures.items():
                try:
                    wait_time = REQUEST_TIMEOUT + 1
                    if key == "longcat_resources":
                        wait_time = LONGCAT_RESOURCE_TIMEOUT + 1
                    results[key] = fut.result(timeout=wait_time)
                except Exception as e:
                    if key.startswith("amap_"):
                        _external_circuit_record("map_search", False, _safe_error_text(e))
                        results[key] = []
                    else:
                        _external_circuit_record("meituan" if key == "longcat_resources" else "weather", False, _safe_error_text(e))
                        msg = MEITUAN_REAL_FRIENDLY_FALLBACK if key == "longcat_resources" else WEATHER_FRIENDLY_FALLBACK
                        results[key] = {"success": False, "message": msg, "error": msg}
        hotels = _attach_item_coords(_real_meituan_items(results.get("hotels", {}), 3), city_name, allow_geocode=False)
        foods = _attach_item_coords(_real_meituan_items(results.get("foods", {}), 6), city_name, allow_geocode=False)
        sights = _attach_item_coords(_real_meituan_items(results.get("sights", {}), 6), city_name, allow_geocode=False)
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
            # 只用高德真实 POI，不再用 _independent_items 区域模板兜底；没有就为空
            foods = _attach_item_coords(results.get("amap_foods") or [], city_name, allow_geocode=False)
        if not sights:
            sights = _attach_item_coords(results.get("amap_sights") or [], city_name, allow_geocode=False)
        if not hotels:
            hotels = _attach_item_coords(results.get("amap_hotels") or [], city_name, allow_geocode=False)
        resource_quality = _resource_data_tier(hotels, foods, sights)
        if resource_quality["tier"] != "A":
            fallback_used = True
    title_suffix = "独立行程规划" if req["intent"] == "no_meituan" else "行程规划"
    if independent:
        resource_quality = _resource_data_tier(hotels, foods, sights)
        recovery_message = ""
        fallback_used = bool(resource_quality.get("area_suggestion_count"))
    for group in (hotels, foods, sights):
        for item in group or []:
            if isinstance(item, dict):
                item.setdefault("query_city", city_name)
    hotels = city_guard_for_candidates(hotels, city_name, "hotels")
    foods = city_guard_for_candidates(foods, city_name, "restaurants")
    sights = city_guard_for_candidates(sights, city_name, "spots")
    resource_quality = _resource_data_tier(hotels, foods, sights)
    days = _build_itinerary_days(city_name, req["days"], sights, foods, primary_transport, budget, pstate, results.get("weather"))
    route_elapsed = time.perf_counter() - plan_started
    if (not ENABLE_FOREGROUND_AMAP_ROUTE) or independent or route_elapsed > max(4.5, AGENT_FINAL_BUDGET_SECONDS - 4.0):
        amap_travel_route = {
            "success": False,
            "message": "快速前台规划已先生成路线卡；地图路线可通过高德链接继续打开。",
            "pois": _select_amap_travel_pois(hotels, foods, sights),
            "points": [],
            **_amap_meta(False, 0),
        }
        amap_route = {"success": False, "message": "快速前台规划未阻塞等待路线段规划", "points": [], **_amap_meta(False, 0)}
    else:
        amap_travel_route = _plan_amap_travel_route(city_name, hotels, foods, sights, primary_transport)
        if time.perf_counter() - plan_started > AGENT_FINAL_BUDGET_SECONDS - 2.0:
            amap_route = {"success": False, "message": "已优先保障 10 秒内生成方案，跳过补充路线段", "points": [], **_amap_meta(False, 0)}
        else:
            amap_route = _plan_amap_route_from_prompt(user_prompt, city_name or city, origin, dest, primary_transport)
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
    queue_monitor = {}
    if re.search(r"不想排队|避开排队|少排队|排队|等位|取号", user_prompt or ""):
        monitor_target = (foods[0].get("name") if foods else f"{city_name}本地餐饮")
        monitor_result = tool_mock_start_service_monitor(
            "queue",
            monitor_target,
            city_name,
            "排队超过20分钟自动切换同区域备选",
            "switch_restaurant_or_call_taxi",
            30,
            {
                "budget": req.get("budget"),
                "persona": pstate.get("keys", []),
                "reason": "用户要求不想排队",
            },
        )
        if monitor_result.get("success"):
            queue_monitor = monitor_result.get("monitor", {})
    soul_summary = str(soul_memory.get("summary", "暂无稳定偏好"))
    if len(soul_summary) > 46:
        soul_summary = soul_summary[:46] + "…"
    day_label = "1日" if int(req.get("days") or 1) == 1 else f"{req['days']}天"
    amap_travel_context = {k: v for k, v in (amap_travel_route or {}).items() if k != "points"}
    amap_travel_context["route_points_count"] = len((amap_travel_route or {}).get("points") or [])
    amap_engine_ok = bool((amap_travel_route or {}).get("success") or (amap_route or {}).get("success"))
    amap_poi_count = int(resource_quality.get("amap_poi_count") or len([x for x in [*hotels, *foods, *sights] if _is_real_map_poi_item(x)]) or 0)
    real_resource_count = sum((resource_quality.get("real_counts") or {}).values())
    amap_error_message = AMAP_LAST_ERROR.get("message") or "高德暂无真实结果，已切换美团/Mock兜底。"
    longcat_resources = results.get("longcat_resources") if isinstance(results.get("longcat_resources"), dict) else {}
    longcat_ok = bool(longcat_resources.get("success"))
    longcat_status = longcat_resources.get("status") or ""
    tool_status = {
        "longcat_resource": {
            "success": longcat_ok,
            "status": "success" if longcat_ok else ("blocked" if longcat_status == "blocked" else ("skipped" if not LONGCAT_API_KEY else "fallback")),
            "message": longcat_resources.get("message") or ("美团龙猫已完成资源意图和关键词排序" if longcat_ok else "美团龙猫暂不可用，已切换备用数据源"),
            "data_source": "longcat",
            "tool_name": "longcat-resource-agent",
            "elapsed_ms": int(longcat_resources.get("elapsed_ms") or 0),
        },
        "meituan_skill": {
            "success": real_resource_count > 0,
            "status": "success" if real_resource_count > 0 else (
                "blocked" if req["user_preference"].get("avoid_meituan")
                else "skipped" if (independent and not (req.get("wants_meituan") or req.get("requires_real_meituan")))
                else "fallback"),
            "message": "美团搜索🔍返回真实资源" if real_resource_count > 0 else (
                "用户要求避开美团" if req["user_preference"].get("avoid_meituan")
                else "普通出游规划未触发美团真实资源，已用快速规划链路" if (independent and not (req.get("wants_meituan") or req.get("requires_real_meituan")))
                else "美团搜索🔍暂未返回真实资源，已切换高德/Mock兜底"),
        },
        "amap_poi": {
            "success": amap_poi_count > 0,
            "status": "success" if amap_poi_count > 0 else "error",
            "count": amap_poi_count,
            "message": f"地图数据返回{amap_poi_count}个真实地点" if amap_poi_count > 0 else amap_error_message,
            "data_source": "amap",
            "tool_name": "amap-lbs-skill",
        },
        "amap_travel_planner": {
            "success": bool((amap_travel_route or {}).get("success")),
            "status": "success" if (amap_travel_route or {}).get("success") else "error",
            "count": len((amap_travel_route or {}).get("pois") or []),
            "message": (amap_travel_route or {}).get("message") or (amap_travel_route or {}).get("error") or ("高德智能旅游规划已完成" if (amap_travel_route or {}).get("success") else amap_error_message),
            "data_source": "amap",
            "tool_name": "amap-lbs-skill",
        },
        "amap_route": {
            "success": bool((amap_route or {}).get("success")),
            "status": "success" if (amap_route or {}).get("success") else "error",
            "message": (amap_route or {}).get("message") or (amap_route or {}).get("error") or ("高德路线规划已完成" if (amap_route or {}).get("success") else amap_error_message),
            "data_source": "amap",
            "tool_name": "amap-lbs-skill",
        },
        "amap_map_link": {
            "success": bool((trip_map_urls or {}).get("gaode")),
            "status": "success" if (trip_map_urls or {}).get("gaode") else "error",
            "message": "高德地图链接生成完成" if (trip_map_urls or {}).get("gaode") else "高德地图链接待生成",
            "data_source": "amap",
            "tool_name": "amap-lbs-skill",
        },
        "mock_queue_monitor": {
            "success": bool(queue_monitor.get("monitor_id")),
            "status": "success" if queue_monitor.get("monitor_id") else "idle",
            "message": f"Mock排队监控已启动：{queue_monitor.get('target_name','')}" if queue_monitor.get("monitor_id") else "未触发排队监控",
            "tool_name": "mock-queue-monitor",
            "data_source": "mock",
        },
    }
    print(
        f"[AMAP_MCP_CALLED] city={city_name} "
        f"travel_success={bool((amap_travel_route or {}).get('success'))} "
        f"route_success={bool((amap_route or {}).get('success'))} "
        f"route_points={len((amap_travel_route or {}).get('points') or (amap_route or {}).get('points') or [])}"
    )
    candidate_pool = {
        "target_city": city_name,
        "normalized_city": search_city_label,
        "spots": sights[:8],
        "restaurants": foods[:8],
        "hotels": hotels[:5],
        "source_status": {
            "spots": len(sights),
            "restaurants": len(foods),
            "hotels": len(hotels),
            "resource_tier": resource_quality.get("tier"),
        },
    }
    planning_context = {
        "user_request": user_prompt,
        "requirements": req,
        "current_date": _dt.now().date().isoformat(),
        "persona": pstate,
        "city": city_name,
        "budget": budget,
        "weather": results.get("weather"),
        "route": {"distance_km": distance_km, "decision": decision, "transport": primary_transport},
        "longcat_resources": longcat_resources,
        "amap_pois": [x for x in [*hotels, *foods, *sights] if _is_real_map_poi_item(x)],
        "amap_travel_route": amap_travel_context,
        "amap_prompt_route": {k: v for k, v in (amap_route or {}).items() if k != "points"},
        "meituan_hotels": [x for x in hotels if _is_real_meituan_item(x)],
        "meituan_restaurants": [x for x in foods if _is_real_meituan_item(x)],
        "meituan_spots": [x for x in sights if _is_real_meituan_item(x)],
        "area_suggestions": [x for x in [*hotels, *foods, *sights] if x.get("is_area_suggestion")],
        "candidate_pool": candidate_pool,
        "data_quality": resource_quality,
        "tool_status": tool_status,
        "queue_monitor": queue_monitor,
        "soul_memory": soul_memory,
        "order": pending_order,
        "intent_card": intent_card,
    }
    route_card = {}
    route_card_source = ""
    route_card_error = ""
    # 质量优先：始终等待 DeepSeek 生成正式 route_map_json；失败时不展示 fast_route_card 模板。
    ds_card = call_deepseek_route_json(
        user_prompt,
        planning_context,
        timeout_seconds=ROUTE_JSON_QUALITY_TIMEOUT,
        max_attempts=2,
    )
    if ds_card.get("data_status") == "insufficient":
        # 真实地点数据不足：如实展示"数据不足"，绝不用模板/城市常识补地点
        route_card_error = (ds_card.get("summary") or "真实地点数据不足，未编造地点。") + "（仅展示地图上可查到的真实地点，请补充地图/美团真实数据后重试）"
        print("[frontend_render_source]insufficient_real_data")
    elif ds_card:
        route_card = _attach_route_map_coords(
            _normalize_trip_plan_json(ds_card, {
                "city": city_name,
                "render_city": city_name,
                "budget": budget,
                "title": f"{city_name}{day_label}{title_suffix}" if independent else f"{city_name} {day_label}{req['budget']}元平台资源行程",
                "summary": f"🍊 {city_name}{day_label}路线地图卡已生成",
            }),
            [*hotels, *foods, *sights],
            city_name,
            allow_geocode=True,
        )
        if _route_city_guard_pass(route_card, city_name, prompt_context_allowed_names := (_route_tool_payload(user_prompt, planning_context).get("allowed_place_names") or [])):
            route_card_source = "deepseek_route_map_json"
            route_card["render_source"] = "路线地图卡"
            route_card["map_engine"] = "地图路线引擎"
        else:
            route_card = {}
            route_card_error = "路线候选点城市不一致，已拦截并改用真实候选池重新生成。"
    if not route_card_source:
        candidate_card = _build_real_candidate_route_card(user_prompt, planning_context)
        if candidate_card.get("route_map"):
            route_card = _attach_route_map_coords(
                _normalize_trip_plan_json(candidate_card, {
                    "city": city_name,
                    "render_city": city_name,
                    "budget": budget,
                    "title": f"{city_name}景点与餐饮路线",
                    "summary": "已根据景点与餐饮建议生成路线卡；点位来自地图参考/候选，需二次确认营业状态。",
                }),
                [*hotels, *foods, *sights],
                city_name,
                allow_geocode=False,
            )
            candidate_names = [s.get("name") for s in (route_card.get("route_map") or []) if s.get("name")]
            if _route_city_guard_pass(route_card, city_name, candidate_names):
                route_card_source = "real_candidate_fallback"
                route_card["render_source"] = "景点与餐饮候选"
                route_card["map_engine"] = "地图路线引擎"
                route_card["generated_from"] = "candidate_cards"
                route_card_error = "已根据景点与餐饮候选生成路线卡。"
                print("[frontend_render_source]real_candidate_fallback")
            else:
                route_card = _strict_insufficient_route(city_name, budget)
                route_card_error = "路线候选点城市不一致，已拦截。"
                route_card_source = "insufficient_real_data"
                print("[frontend_render_source]insufficient_real_data")
        else:
            route_card = candidate_card
            route_card_error = candidate_card.get("summary") or "真实地点数据不足，未编造地点。"
            route_card_source = "food_heavy_insufficient" if candidate_card.get("data_status") == "food_heavy_insufficient" else "insufficient_real_data"
            print(f"[frontend_render_source]{route_card_source}")
    tool_status["deepseek_route_json"] = {
        "success": route_card_source in ("deepseek_route_map_json", "real_candidate_fallback"),
        "status": "success" if route_card_source in ("deepseek_route_map_json", "real_candidate_fallback") else ("idle" if route_card_source == "insufficient_real_data" else "error"),
        "message": "路线地图卡已生成" if route_card_source in ("deepseek_route_map_json", "real_candidate_fallback") else (route_card_error or "真实候选点不足，暂不生成路线卡。"),
        "data_source": "route_card",
        "tool_name": "route-card-builder",
    }
    # 每日行程卡也只用真实 route_map 派生，杜绝人格模板兜底；无真实路线则不展示每日卡，绝不编造。
    if route_card_source == "deepseek_route_map_json":
        days = _days_from_route_map(route_card.get("route_map") or [], budget, req["days"])
    else:
        days = []
    route_map = route_card.get("route_map") if isinstance(route_card, dict) else []
    route_step_items = [
        {"name": s.get("name"), "lat": s.get("lat"), "lng": s.get("lng"), "category": "route_step"}
        for s in (route_map or [])
        if _coerce_float(s.get("lat")) is not None and _coerce_float(s.get("lng")) is not None
    ]
    trip_route_points = (amap_travel_route.get("points") or amap_route.get("points") or route_step_items or [
        {"lat": origin.get("lat"), "lng": origin.get("lng")},
        {"lat": dest.get("lat"), "lng": dest.get("lng")},
    ])
    map_data = _build_map_data(dest, trip_route_points, [
        {"category": "route_step", "items": route_step_items},
        {"category": "origin", "items": [origin]},
        {"category": "destination", "items": [dest]},
        {"category": "hotel", "items": hotels},
        {"category": "food", "items": foods},
        {"category": "sight", "items": sights},
    ])
    planning_context["route_card_source"] = route_card_source
    return {
        "success": True,
        "type": "independent_trip_plan" if independent else "meituan_trip_plan",
        "city": city_name,
        "render_city": city_name,
        "intent": req["intent"],
        "commerce_mode": req["commerce_mode"],
        "planner_mode": req["planner_mode"],
        "user_preference": req["user_preference"],
        "cta": req["cta"],
        "persona_state": pstate,
        "proactive_defaults": proactive,
        "persona": ",".join(pstate.get("keys", [])),
        "persona_label": " + ".join(pstate.get("labels", [])),
        "intent_card": intent_card,
        "title": f"{city_name}{day_label}{title_suffix}" if independent else f"{city_name} {day_label}{req['budget']}元平台资源行程",
        "summary": f"已根据预算、路线和{'+'.join(pstate.get('labels', []))}自动完成独立行程规划。" if independent else f"核心需求已锁定：{city_name}、{day_label}、总预算{req['budget']}元，并按{'+'.join(pstate.get('labels', []))}联动平台资源。",
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
        "longcat_resources": longcat_resources,
        "days": days,
        "route_card": route_card,
        "route_map": route_map or [],
        "route_card_source": route_card_source,
        "frontend_render_source": route_card_source,
        "route_card_error": route_card_error,
        "budget": budget,
        "fallback_used": fallback_used,
        "fallback_message": (recovery_message or "🍊 已从多源精选推荐，区域建议已用位置标注。") if fallback_used else "",
        "data_quality": resource_quality,
        "tool_status": tool_status,
        "planning_context": planning_context,
        "map_provider": _detect_map_provider(user_prompt, map_provider or "gaode"),
        "map_urls": trip_map_urls,
        "flight_query": flight_query,
        "amap_route": amap_route,
        "amap_travel_route": amap_travel_route,
        "map_engine": "地图路线引擎" if (amap_travel_route.get("success") or amap_route.get("success")) else "地图路线暂未返回 · 备用链接",
        "route_source": "amap_travel_planner" if amap_travel_route.get("success") else ("amap_primary" if amap_route.get("success") else "map_link_only"),
        "poi_source": (
            "高德 + 美团"
            if any(_is_real_map_poi_item(x) for x in [*hotels, *foods, *sights]) and any(_is_real_meituan_item(x) for x in [*hotels, *foods, *sights])
            else ("地图参考" if any(_is_real_map_poi_item(x) for x in [*hotels, *foods, *sights]) else ("美团搜索🔍" if any(_is_real_meituan_item(x) for x in [*hotels, *foods, *sights]) else "区域建议"))
        ),
        "map_data": map_data,
        "pending_order": pending_order,
        "queue_monitor": queue_monitor,
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
            tool_status["longcat_resource"]["message"],
            tool_status["meituan_skill"]["message"],
            f"已按距离判定主交通：{decision.get('priority')}",
            tool_status["amap_poi"]["message"],
            tool_status["amap_travel_planner"]["message"],
            tool_status["amap_route"]["message"],
            tool_status["amap_map_link"]["message"],
            tool_status["deepseek_route_json"]["message"],
            tool_status["mock_queue_monitor"]["message"] if queue_monitor else "未触发排队监控；需要时可开启后台监控",
            "已接入航班查询入口" if flight_query.get("enabled") else "当前距离无需航班查询",
            "已生成待确认订单，等待用户确认" if pending_order else ("未生成订单：当前不是完整真实资源规划" if not independent else "无需订单动作，保留规划闭环"),
            "天气已作为辅助信息补充，未覆盖行程主线",
        ],
        "planner_route": {
            "selected": "independent_trip_planner" if independent else "meituan_commerce_planner",
            "called_tools": (
                ["deepseek_intent", "longcat_resource_search"]
                + ((["call_meituan_skill"] if independent and not req["user_preference"].get("avoid_meituan") else []) if independent else ["call_meituan_skill"])
                + ["amap_poi", "amap_travel_planner", "amap_route", "amap_map_link", "deepseek_route_json"]
                + (["mock_start_service_monitor"] if queue_monitor else [])
                + (["create_pending_order"] if pending_order else [])
            ),
            "blocked": (["plan_meituan_trip", "call_meituan_skill"] if req["user_preference"].get("avoid_meituan") else ["meituan_order_flow"]) if independent else [],
            "reason": ("avoid_meituan=true，使用独立行程规划" if req["user_preference"].get("avoid_meituan") else "用户未要求美团交易，默认使用独立行程规划") if independent else "用户需要平台资源推荐",
        },
        "meituan_note": "已根据预算和路线自动完成独立行程规划" if independent else (("美团搜索🔍 未返回完整真实资源，区域建议已明确标注" if fallback_used else "已按你的要求联动美团实时资源")),
        "fixed_sections": ["用户意图理解卡", "行程速览", "天气速览卡片", "景点与餐饮建议" if req["commerce_mode"] == "none" else "美团酒店推荐", "几天行程路线卡片", "综合结论"],
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
    return (city_hint or "").replace("市", "").strip()

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
        "gaode": _amap_map_link(
            f"https://www.amap.com/dir?from[name]={origin}&to[name]={destination}&type=walk",
            city=city,
            origin=first,
            destination=last,
        ),
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
    if not city:
        return {
            "success": False,
            "type": "weekend_plan",
            "city": "",
            "data_status": "insufficient",
            "error": "还没有明确目的地，无法生成真实路线。请先告诉我要去哪个城市或区域。",
            "route_card": _strict_insufficient_route("目的地待确认"),
        }
    # 真实数据优先：周末/半日入口也统一委托正式行程管线。
    # 旧的 WEEKEND_CITY_PLANS 仅保留作调试参考，不再进入用户可见结果。
    strict_plan = tool_plan_meituan_trip(city, user_prompt, persona, map_provider)
    route_card = strict_plan.get("route_card") if isinstance(strict_plan, dict) else {}
    route_map = route_card.get("route_map") if isinstance(route_card, dict) else []
    if isinstance(route_map, list) and route_map:
        metrics = route_card.get("metrics") if isinstance(route_card.get("metrics"), dict) else {}
        stops = []
        for idx, step in enumerate(route_map[:4], 1):
            stops.append({
                "order": idx,
                "name": step.get("name", ""),
                "tag": step.get("type", ""),
                "duration": f"{step.get('stay_minutes', 60)}min",
                "note": step.get("short_desc") or step.get("reason") or "来自真实工具结果",
                "time": step.get("arrival_time") or step.get("time") or "",
                "lat": step.get("lat"),
                "lng": step.get("lng"),
            })
        return {
            "success": True,
            "type": "weekend_plan",
            "city": route_card.get("city") or city,
            "title": route_card.get("title") or route_card.get("route_title") or f"{city}周末出行方案",
            "summary": route_card.get("summary") or "已基于真实地点生成周末方案",
            "route": {
                "name": route_card.get("title") or "真实地点路线",
                "distance_km": metrics.get("total_distance_km") or metrics.get("distance_km") or "",
                "duration_min": metrics.get("total_duration_minutes") or "",
                "mode": "mixed",
            },
            "stops": stops,
            "activities": [],
            "route_card": route_card,
            "data_status": route_card.get("data_status", "sufficient"),
            "delegated_to": "plan_meituan_trip",
        }
    return {
        "success": False,
        "type": "weekend_plan",
        "city": city,
        "data_status": "insufficient",
        "error": (route_card.get("summary") if isinstance(route_card, dict) else "") or "真实地点数据不足，不生成模板周末路线。",
        "route_card": route_card if isinstance(route_card, dict) else _strict_insufficient_route(city),
        "delegated_to": "plan_meituan_trip",
    }
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
def _weather_from_loc(loc: dict) -> dict:
    cache_key = _weather_cache_key(loc)
    cached = _weather_cached(cache_key, WEATHER_CACHE_TTL_SECONDS)
    if cached:
        return cached
    if _external_circuit_open("weather"):
        return _weather_fallback_result(loc, "weather_circuit_open")
    try:
        r=_HTTP_SESSION.get(OM_WEATHER_URL,params={
            "latitude":loc["lat"],"longitude":loc["lng"],
            "current":"temperature_2m,apparent_temperature,weather_code,wind_speed_10m,wind_direction_10m,relative_humidity_2m",
            "timezone":"auto","forecast_days":1},timeout=REQUEST_TIMEOUT)
        r.raise_for_status()
        curr=r.json().get("current",{})
        wcode=int(curr.get("weather_code",0))
        temp=round(float(curr.get("temperature_2m",20)))
        feels=round(float(curr.get("apparent_temperature",temp)))
        rh=round(float(curr.get("relative_humidity_2m",50)))
        cd=loc.get("name") or "当前位置"
        if loc.get("country") and loc["country"] not in ("中国",):
            cd=f"{cd}({loc['country']})"
        result = {"success":True,"city":cd,"data":{
            "text":WMO_ZH.get(wcode,"未知"),"temp":temp,"feels_like":feels,
            "wind_dir":_deg_to_dir(curr.get("wind_direction_10m",0)),
            "wind_class":_kmh_to_level(curr.get("wind_speed_10m",0)),"rh":rh}}
        _weather_store(cache_key, result)
        _external_circuit_record("weather", True)
        return result
    except Exception as e:
        _external_circuit_record("weather", False, _safe_error_text(e))
        return _weather_fallback_result(loc, e)


def tool_get_weather_by_coords(lat: float, lng: float, name: str = "当前位置") -> dict:
    try:
        loc = {"lat": float(lat), "lng": float(lng), "name": name or "当前位置", "country": ""}
    except (TypeError, ValueError):
        return {"success": False, "error": "lat/lng 参数无效"}
    return _weather_from_loc(loc)


def tool_get_weather(city: str) -> dict:
    ck=city.replace("市","").replace("省","").strip()
    known = CITY_GEO_INDEX.get(_city_alias(ck))
    loc = {"lat":known["lat"],"lng":known["lng"],"name":known["name"],"country":known["country"]} if known else None
    if not loc:
        loc=geocode_openmeteo(ck)
    if not loc:
        c=geocode_baidu(ck)
        if c: loc={"lat":c["lat"],"lng":c["lng"],"name":ck,"country":"中国"}
    if not loc: return {"success":False,"friendly":True,"error":WEATHER_FRIENDLY_FALLBACK,"message":WEATHER_FRIENDLY_FALLBACK}
    return _weather_from_loc(loc)


def _format_amap_plan_route(amap_route: dict, city: str, start_name: str, dest_name: str,
                            persona: str = "", route_profile: str = "") -> dict:
    origin_loc = _extract_coord_pair(amap_route.get("origin"))
    dest_loc = _extract_coord_pair(amap_route.get("destination"))
    route_points = amap_route.get("points") or []
    if not route_points and origin_loc and dest_loc:
        route_points = [origin_loc, dest_loc]
    duration_min = max(1, round(int(amap_route.get("duration_sec") or 0) / 60)) if amap_route.get("duration_sec") else 0
    distance_m = int(amap_route.get("distance_m") or 0)
    start_obj = {"name": start_name, **(origin_loc or {})}
    dest_obj = {"name": dest_name, **(dest_loc or {})}
    rp = _resolve_route_profile(route_profile, persona)
    return {
        "success": True,
        "mode": amap_route.get("mode") or "riding",
        "data_source": "amap",
        "tool_name": "amap-lbs-skill",
        "elapsed_ms": amap_route.get("elapsed_ms", 0),
        "route_source": "amap_fallback",
        "map_engine": "地图路线引擎",
        "persona": persona or "",
        "persona_label": PERSONA_LABELS.get((persona or "").strip().lower(), ""),
        "route_profile": rp,
        "route_profile_meta": _route_profile_meta(rp, duration_min),
        "start": start_obj,
        "destination": dest_obj,
        "map_data": _build_map_data(dest_obj, route_points, [
            {"category": "start", "items": [start_obj]},
            {"category": "destination", "items": [dest_obj]},
        ]),
        "route": {
            "distance_m": distance_m,
            "distance_km": round(distance_m / 1000, 2) if distance_m else 0,
            "duration_sec": int(amap_route.get("duration_sec") or 0),
            "duration_min": duration_min,
            "steps": amap_route.get("steps") or [],
            "points": route_points,
        },
    }

def tool_plan_route(city: str, start: str, destination: str,
                    riding_type: int = 0, road_prefer: Optional[int] = None,
                    route_profile: str = "", persona: str = "",
                    route_strategy: str = "") -> dict:
    rp = _resolve_route_profile(route_profile, persona)
    profile_cfg = ROUTE_PROFILES[rp]
    road_prefer = profile_cfg["road_prefer"] if road_prefer is None else int(road_prefer)
    cache_payload = {
        "tool_plan_route": {
            "city": city, "start": start, "destination": destination,
            "riding_type": riding_type, "road_prefer": road_prefer,
            "route_profile": rp, "persona": persona, "route_strategy": route_strategy,
        }
    }
    cached = _external_cache_get("map_route", cache_payload)
    if cached is not None:
        return cached
    sn=start or f"{city}人民广场"
    start_coord = _parse_lat_lng(sn)
    oc=start_coord or geocode_baidu(sn,city)
    start_name = "当前位置" if start_coord else sn
    dc=geocode_baidu(destination,city)
    if not oc or not dc:
        amap = route_amap(sn, destination, "riding", city)
        if amap.get("success"):
            out = _format_amap_plan_route(amap, city, start_name, destination, persona, route_profile)
            _external_cache_set("map_route", cache_payload, out)
            return out
        return {"success":False,"error":MAP_ROUTE_FRIENDLY_FALLBACK,"message":MAP_ROUTE_FRIENDLY_FALLBACK}
    if _external_circuit_open("baidu_map"):
        amap = route_amap(sn, destination, "riding", city)
        if amap.get("success"):
            out = _format_amap_plan_route(amap, city, start_name, destination, persona, route_profile)
            _external_cache_set("map_route", cache_payload, out)
            return out
    try:
        r=requests.get(BAIDU_RIDING_URL,params={
            "origin":f"{oc['lat']},{oc['lng']}","destination":f"{dc['lat']},{dc['lng']}",
            "riding_type":riding_type,"road_prefer":road_prefer,
            "steps_info":1,"ret_coordtype":"bd09ll","ak":BAIDU_AK},timeout=REQUEST_TIMEOUT)
        d=r.json()
    except Exception as e:
        _external_circuit_record("baidu_map", False, _safe_error_text(e))
        amap = route_amap(sn, destination, "riding", city)
        if amap.get("success"):
            out = _format_amap_plan_route(amap, city, start_name, destination, persona, route_profile)
            _external_cache_set("map_route", cache_payload, out)
            return out
        return {"success":False,"error":MAP_ROUTE_FRIENDLY_FALLBACK,"message":MAP_ROUTE_FRIENDLY_FALLBACK}
    if d.get("status")!=0:
        _external_circuit_record("baidu_map", False, d.get("message", "route_failed"))
        amap = route_amap(sn, destination, "riding", city)
        if amap.get("success"):
            out = _format_amap_plan_route(amap, city, start_name, destination, persona, route_profile)
            _external_cache_set("map_route", cache_payload, out)
            return out
        return {"success":False,"error":MAP_ROUTE_FRIENDLY_FALLBACK,"message":MAP_ROUTE_FRIENDLY_FALLBACK}
    _external_circuit_record("baidu_map", True)
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
    out = {"success":True,
        "mode": "riding",
        "route_source": "baidu",
        "map_engine": "百度",
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
    _external_cache_set("map_route", cache_payload, out)
    return out


_CITY_MAP = {
    "新加坡":"Singapore","上海":"Shanghai","北京":"Beijing","香港":"Hong Kong",
    "东京":"Tokyo","首尔":"Seoul","纽约":"New York","巴黎":"Paris",
    "伦敦":"London","曼谷":"Bangkok","台北":"Taipei","澳门":"Macau",
    "广州":"Guangzhou","成都":"Chengdu","深圳":"Shenzhen","大阪":"Osaka",
    "京都":"Kyoto","米兰":"Milan","罗马":"Rome","巴塞罗那":"Barcelona",
    "苏州":"Suzhou","杭州":"Hangzhou","南京":"Nanjing","重庆":"Chongqing",
    "西安":"Xi'an","武汉":"Wuhan","长沙":"Changsha","青岛":"Qingdao",
    "厦门":"Xiamen","天津":"Tianjin","三亚":"Sanya","大连":"Dalian",
    "沈阳":"Shenyang","哈尔滨":"Harbin",
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
        return {"success":False,"error":"米其林知识库和本地CSV均不可用"}
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
        lines.append("说明：向量检索暂时不可用，已自动切换本地CSV检索，演示结果不断线。")
    return {
        "success": True,
        "answer": _clean_markdown("\n".join(lines)),
        "references": refs,
        "fallback": True,
        "rag_error": rag_error,
    }


def tool_search_michelin(query: str) -> dict:
    if not MICHELIN_AVAILABLE:
        return _michelin_csv_fallback(query, rag_error=MICHELIN_IMPORT_ERROR or "米其林知识库模块未加载")
    try:
        result = ask_michelin(_enhance_query(query))
        return {"success":True,"answer":_clean_markdown(result["answer"]),"references":result["references"]}
    except Exception as e:
        return _michelin_csv_fallback(query, rag_error=_safe_error_text(e))


_BLACK_PEARL_CACHE = {"path": "", "mtime": 0.0, "text": "", "error": ""}
_BLACK_PEARL_SG_RAG_CACHE = {"path": "", "mtime": 0.0, "rag": None}
_BLACK_PEARL_CHAR_MAP = str.maketrans({
    "⻓": "长",
    "⻘": "青",
    "⻔": "门",
    "⻥": "鱼",
    "⻋": "车",
    "⻝": "食",
    "⻰": "龙",
    "⻩": "黄",
})


def _extract_black_pearl_pdf_text(path: str) -> str:
    """Extract text from the Black Pearl/Michelin PDF with optional local readers."""
    reader_errors = []
    for mod_name in ("pypdf", "PyPDF2"):
        try:
            mod = __import__(mod_name)
            reader = mod.PdfReader(path)
            text = "\n".join((page.extract_text() or "") for page in reader.pages)
            if text.strip():
                return text
        except Exception as e:
            reader_errors.append(f"{mod_name}:{_safe_error_text(e)}")
    try:
        import pdfplumber
        with pdfplumber.open(path) as pdf:
            text = "\n".join((page.extract_text() or "") for page in pdf.pages)
        if text.strip():
            return text
    except Exception as e:
        reader_errors.append(f"pdfplumber:{_safe_error_text(e)}")
    try:
        proc = subprocess.run(
            ["pdftotext", path, "-"],
            capture_output=True,
            text=True,
            timeout=12,
            check=False,
        )
        if proc.stdout.strip():
            return proc.stdout
        if proc.stderr.strip():
            reader_errors.append(f"pdftotext:{_safe_error_text(proc.stderr)}")
    except Exception as e:
        reader_errors.append(f"pdftotext:{_safe_error_text(e)}")
    raise RuntimeError("PDF文本提取失败：" + "；".join(reader_errors[-3:]))


def _load_black_pearl_pdf_text() -> tuple[str, str, str]:
    path = BLACK_PEARL_PDF_PATH
    if not os.path.exists(path):
        return "", path, f"未找到PDF文件：{path}"
    try:
        mtime = os.path.getmtime(path)
        if (_BLACK_PEARL_CACHE.get("path") == path
                and _BLACK_PEARL_CACHE.get("mtime") == mtime
                and _BLACK_PEARL_CACHE.get("text")):
            return _BLACK_PEARL_CACHE["text"], path, ""
        text = unicodedata.normalize("NFKC", _extract_black_pearl_pdf_text(path)).translate(_BLACK_PEARL_CHAR_MAP)
        text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f-\x9f]", " ", text)
        _BLACK_PEARL_CACHE.update({"path": path, "mtime": mtime, "text": text, "error": ""})
        return text, path, ""
    except Exception as e:
        err = _safe_error_text(e)
        _BLACK_PEARL_CACHE.update({"path": path, "mtime": 0.0, "text": "", "error": err})
        return "", path, err


def _query_black_pearl_singapore_xlsx(query: str) -> dict:
    path = BLACK_PEARL_SINGAPORE_XLSX_PATH
    if not os.path.exists(path):
        return {"success": False, "error": f"未找到新加坡黑珍珠Excel：{path}"}
    try:
        from hei_zhen_zhu_local import RAGDocument, SimpleRAGSystem, read_black_pearl_singapore_xlsx
        mtime = os.path.getmtime(path)
        rag = _BLACK_PEARL_SG_RAG_CACHE.get("rag")
        if (
            not rag
            or _BLACK_PEARL_SG_RAG_CACHE.get("path") != path
            or _BLACK_PEARL_SG_RAG_CACHE.get("mtime") != mtime
        ):
            text = read_black_pearl_singapore_xlsx(path)
            docs = [
                RAGDocument(
                    text=line,
                    source=os.path.basename(path),
                    metadata={"kind": "black_pearl_singapore_xlsx", "chunk_id": idx, "city": "新加坡"},
                )
                for idx, line in enumerate(text.splitlines())
                if line.strip()
            ]
            if not docs:
                return {"success": False, "error": "新加坡黑珍珠Excel暂无可检索文本"}
            rag = SimpleRAGSystem(model_name=None)
            rag.fit(docs)
            _BLACK_PEARL_SG_RAG_CACHE.update({"path": path, "mtime": mtime, "rag": rag})
        rag.memory.messages = []
        return rag.ask(query, top_k=4).to_dict()
    except Exception as e:
        return {"success": False, "error": _safe_error_text(e)}


def _black_pearl_query_terms(query: str) -> list[str]:
    query = unicodedata.normalize("NFKC", str(query or ""))
    raw = re.findall(r"[\u4e00-\u9fff]{2,}|[A-Za-z0-9]+", query)
    stop = {"黑珍珠", "米其林", "餐厅", "美食", "推荐", "哪些", "哪里", "附近", "查询", "帮我", "一下"}
    terms = []
    for term in raw:
        if term in stop:
            continue
        if term not in terms:
            terms.append(term)
    return terms[:12]


def _black_pearl_chunks(text: str) -> list[str]:
    clean = re.sub(r"[ \t]+", " ", str(text or ""))
    parts = [p.strip() for p in re.split(r"\n{2,}|(?=【[^】]{1,24}】)|(?=##\s*)", clean) if len(p.strip()) >= 20]
    if len(parts) >= 3:
        return parts
    flat = re.sub(r"\s+", " ", clean).strip()
    chunks = []
    size, overlap = 760, 120
    for start in range(0, len(flat), size - overlap):
        chunk = flat[start:start + size].strip()
        if len(chunk) >= 40:
            chunks.append(chunk)
    return chunks


def tool_search_black_pearl(query: str) -> dict:
    """Search the local 黑珍珠-米其林.pdf and answer only from PDF context."""
    try:
        singapore_query = bool(re.search(r"新加坡|singapore", str(query or ""), re.I))
        if singapore_query:
            rag_result = _query_black_pearl_singapore_xlsx(query)
            source_path = BLACK_PEARL_SINGAPORE_XLSX_PATH
        else:
            from hei_zhen_zhu_local import query_black_pearl_pdf
            rag_result = query_black_pearl_pdf(query)
            source_path = BLACK_PEARL_PDF_PATH
        answer = _clean_markdown(rag_result.get("answer", ""))
        hits = rag_result.get("hits") or []
        if answer and hits:
            return {
                "success": True,
                "answer": answer,
                "references": rag_result.get("references", [os.path.basename(source_path)]),
                "source": source_path,
                "contexts": [h.get("text", "") for h in hits if isinstance(h, dict)],
                "structured": rag_result.get("structured", {}),
                "vector_rag": True,
            }
    except Exception as e:
        print(f"[BLACK_PEARL_VECTOR_RAG_FALLBACK] {_safe_error_text(e)}")

    text, path, err = _load_black_pearl_pdf_text()
    if not text:
        return {"success": False, "error": err or "黑珍珠PDF暂无可检索文本", "source": path}

    detected_cities = [c.replace("市", "") for c in re.findall(_CITY_PAT, str(query or "")) if c]
    search_text = text
    for city_name in detected_cities:
        m = re.search(rf"{re.escape(city_name)}\s*[-—－]\s*黑珍珠[:：]", text)
        if not m:
            continue
        next_m = re.search(r"(?:^|\n)\s*[\u2e80-\u9fff]{1,8}\s*[-—－]\s*黑珍珠[:：]", text[m.end():])
        end = (m.end() + next_m.start()) if next_m else len(text)
        search_text = text[m.start():end]
        break

    chunks = _black_pearl_chunks(search_text)
    terms = _black_pearl_query_terms(query)
    scored = []
    for i, chunk in enumerate(chunks):
        compact = re.sub(r"\s+", " ", chunk)
        score = 0
        for term in terms:
            score += compact.count(term) * 6
        for city_name in detected_cities:
            if city_name and city_name in compact:
                score += 180
            if city_name and re.search(rf"{re.escape(city_name)}\s*[-—－]\s*黑珍珠", compact):
                score += 260
        if re.search(r"黑珍珠|钻|星|人均|¥|￥|餐厅|米其林", compact):
            score += 3
        if score > 0:
            scored.append((score, i, compact))
    if not scored:
        scored = [(0, i, re.sub(r"\s+", " ", c)) for i, c in enumerate(chunks[:5])]
    top = [c for _, _, c in sorted(scored, key=lambda x: (-x[0], x[1]))[:4]]
    context = "\n\n".join(top)

    if DEEPSEEK_API_KEY or LONGCAT_API_KEY:
        try:
            resp = _llm_chat_completion({
                "messages": [
                    {
                        "role": "system",
                        "content": (
                            "你是黑珍珠/米其林餐厅检索助手。只能依据用户给定的PDF检索片段回答，"
                            "不得编造PDF片段之外的餐厅、价格、星级或地址。资料不足时说未在PDF中检索到足够信息。"
                        ),
                    },
                    {
                        "role": "user",
                        "content": f"用户问题：{query}\n\nPDF检索片段：\n{context}",
                    },
                ],
                "max_tokens": 900,
                "temperature": 0.1,
            }, purpose="black_pearl_pdf_rag")
            answer = _clean_markdown(resp.json()["choices"][0]["message"].get("content", ""))
            if answer:
                return {
                    "success": True,
                    "answer": answer,
                    "references": [os.path.basename(path)],
                    "source": path,
                    "contexts": top,
                }
        except Exception as e:
            print(f"[BLACK_PEARL_PDF_RAG_FALLBACK] {_safe_error_text(e)}")

    snippets = []
    for idx, chunk in enumerate(top, 1):
        snippets.append(f"{idx}. {chunk[:220]}{'…' if len(chunk) > 220 else ''}")
    return {
        "success": True,
        "answer": _clean_markdown("已基于《黑珍珠-米其林.pdf》完成本地检索：\n" + "\n".join(snippets)),
        "references": [os.path.basename(path)],
        "source": path,
        "contexts": top,
        "fallback": True,
    }


def _looks_black_pearl_intent(text: str) -> bool:
    return bool(re.search(r"黑珍珠|black\s*pearl", str(text or ""), re.I))


def _looks_michelin_intent(text: str) -> bool:
    return bool(re.search(r"米其林|michelin|一星|二星|三星|摘星", str(text or ""), re.I))


def _looks_generic_premium_dining(text: str) -> bool:
    return bool(re.search(
        r"高端餐饮|高端餐厅|高级餐厅|星级餐厅|榜单餐厅|fine\s*dining|纪念日餐厅|贵一点的餐厅|好一点的餐厅",
        str(text or ""),
        re.I,
    ))


def _premium_query_city_scope(query: str, city_hint: str = "") -> tuple[str, bool]:
    """Return (city, explicit). Explicit user destination beats current city."""
    s = re.sub(r"\[[^\]]*坐标[^\]]*\]|（[^）]*坐标[^）]*）", "", str(query or ""))
    points = _extract_trip_points(s, "")
    dest = _city_alias(_clean_place_token(points.get("destination", "")))
    if dest and dest != "本地":
        return dest, True
    matches = []
    for m in re.finditer(_CITY_PAT, s):
        city = _city_alias(m.group(1))
        if city and city not in [x[1] for x in matches]:
            matches.append((m.start(), city))
    if matches:
        # 多城市时取后出现的城市，避免“我在上海，帮我看新加坡米其林”被上海覆盖。
        return matches[-1][1], True
    hint = _city_alias(_clean_place_token(city_hint or ""))
    if hint and hint != "上海":
        return hint, False
    coords = _parse_lat_lng(query)
    if coords:
        located_city = _nearest_city_from_coords(coords["lat"], coords["lng"], "")
        if located_city:
            return located_city, False
    return "", False

def _premium_non_default_city(city: str, query: str = "") -> str:
    hint = _city_alias(_clean_place_token(city or ""))
    if hint == "上海" and not re.search(r"上海|shanghai", str(query or ""), re.I):
        return ""
    return hint

def _premium_guide_label(text: str, default: str = "Restaurant Guide") -> str:
    s = str(text or "")
    if re.search(r"黑珍珠|black\s*pearl", s, re.I):
        return "BlackPearl"
    if re.search(r"米其林|michelin|一星|二星|三星|star", s, re.I):
        return "Michelin"
    return default

def _premium_clean_line(text: str) -> str:
    s = unicodedata.normalize("NFKC", str(text or "")).translate(_BLACK_PEARL_CHAR_MAP)
    s = re.sub(r"^\s*\d+\s*[.、)]\s*", "", s)
    s = re.sub(r"\[\d+\]", "", s)
    s = re.sub(r"\s+", " ", s).strip(" |｜-—:：")
    return s

def _premium_user_safe_text(text: str) -> str:
    s = _clean_markdown(text or "")
    s = re.sub(r"(?i)rag_documents\.csv|source_file|embedding|vector|chunk|RAG|rag", "", s)
    s = re.sub(r"(?i)本地知识库|知识库检索|检索结果|原文片段|向量库", "餐厅资料", s)
    s = re.sub(r"\[\d+\]", "", s)
    s = re.sub(r"根据\s*餐厅资料\s*，?可以这样回答[:：]?", "", s)
    return _clean_markdown(s)

def _premium_raw_chunks(result: dict) -> list[str]:
    chunks = []
    for value in result.get("contexts") or []:
        if value:
            chunks.append(str(value))
    answer = result.get("answer")
    if answer:
        chunks.append(str(answer))
    structured = result.get("structured")
    if isinstance(structured, dict):
        for key in ("restaurants", "items", "cards"):
            if isinstance(structured.get(key), list):
                for item in structured[key]:
                    chunks.append(json.dumps(item, ensure_ascii=False) if isinstance(item, dict) else str(item))
    return [c for c in chunks if c and c.strip()]

def _premium_field(text: str, patterns: list[str]) -> str:
    for pat in patterns:
        m = re.search(pat, text, re.I)
        if m:
            return _premium_clean_line(m.group(1))[:90]
    return ""

def _premium_city_matches(card: dict, target_city: str) -> bool:
    target = _city_alias(_clean_place_token(target_city or ""))
    if not target:
        return True
    aliases = {target, target.replace("市", "")}
    if target in _CITY_MAP:
        aliases.add(_CITY_MAP[target])
    low_aliases = {a.lower() for a in aliases if a}
    hay = " ".join(str(card.get(k) or "") for k in ("city", "area", "address", "name", "_raw")).lower()
    return any(a.lower() in hay for a in low_aliases)

def _looks_restaurant_name(value: str) -> bool:
    s = _premium_clean_line(value)
    if not s or len(s) > 60:
        return False
    if _city_alias(s) in CITY_GEO_INDEX and len(s.split()) <= 3:
        return False
    if re.search(r"餐厅[（(]\d+\s*家[）)]|^\d+\s*家", s):
        return False
    if re.search(r"^https?://|guide\.michelin|restaurant in|according to|根据|检索|参考|来源|数据源|本地|知识库", s, re.I):
        return False
    if re.search(r"为您精选|满足不同需求|以下|以上|可以这样回答|需二次确认", s):
        return False
    return bool(re.search(r"[\u4e00-\u9fffA-Za-z]", s))

def _restaurant_card(name: str, city: str, guide: str, level: str = "",
                     cuisine: str = "", avg_price: str = "", area: str = "",
                     address: str = "", reason: str = "", recommended_for: str = "",
                     raw: str = "") -> dict:
    return {
        "name": _premium_clean_line(name),
        "city": _city_alias(_clean_place_token(city or "")),
        "guide": guide or "Restaurant Guide",
        "level": _premium_clean_line(level),
        "cuisine": _premium_clean_line(cuisine),
        "avg_price": _premium_clean_line(avg_price),
        "area": _premium_clean_line(area),
        "address": _premium_clean_line(address),
        "recommended_for": _premium_clean_line(recommended_for or "纪念日 / 高端聚餐 / 旅行体验"),
        "reason": _premium_clean_line(reason or "来自榜单餐厅资料，适合高端餐饮参考。"),
        "need_verify": True,
        "can_order": False,
        "_raw": raw,
    }

def _extract_pipe_restaurant(line: str, query: str, guide: str, city_hint: str) -> dict | None:
    text = _premium_clean_line(line)
    if not text or ("|" not in text and "｜" not in text):
        return None
    name = _premium_field(text, [r"餐厅名称\s*[:：]\s*([^|｜\n]+)", r"(?:^|[|｜])\s*name\s*[:：]\s*([^|｜\n]+)"])
    cuisine = _premium_field(text, [r"菜系\s*[:：]\s*([^|｜\n]+)", r"cuisine\s*[:：]\s*([^|｜\n]+)"])
    level = _premium_field(text, [r"钻级\s*[:：]\s*([^|｜\n]+)", r"(?:award|星级)\s*[:：]\s*([^|｜\n]+)"])
    price = _premium_field(text, [r"人均消费?约?\s*([¥￥]?\s*[0-9—-]+)", r"人均\s*([¥￥]?\s*[0-9—-]+)"])
    city = _premium_field(text, [r"地点\s*[:：]\s*([^|｜\n]+)", r"城市\s*[:：]\s*([^|｜\n]+)"]) or city_hint
    address = _premium_field(text, [r"地址\s*[:：]\s*([^|｜\n]+)"])
    parts = [_premium_clean_line(p) for p in re.split(r"[|｜]", text) if _premium_clean_line(p)]
    if not name:
        if len(parts) >= 5 and _looks_restaurant_name(parts[0]) and not re.search(r"^https?://|\.com|selected restaurants", parts[0], re.I):
            name = parts[0]
            address = address or parts[1]
            city = city or parts[2]
            price = price or parts[3]
            cuisine = cuisine or parts[4]
            level = level or next((p for p in parts if re.search(r"star|Bib|Selected|一星|二星|三星", p, re.I)), "")
        else:
            for idx, part in enumerate(parts):
                if _looks_restaurant_name(part) and not re.search(r"^https?://|\.com|air conditioning|wheelchair|selected restaurants|^\d+$", part, re.I):
                    tail = " ".join(parts[idx:idx + 4])
                    if re.search(r"restaurant|cuisine|sushi|french|chinese|japanese|korean|italian|modern|contemporary|中餐|日料|法餐|菜", tail, re.I):
                        name = part
                        cuisine = cuisine or (parts[idx + 1] if idx + 1 < len(parts) else "")
                        city = city or (parts[idx + 2] if idx + 2 < len(parts) else city_hint)
                        address = address or (parts[idx + 3] if idx + 3 < len(parts) else "")
                        break
    if not name or not _looks_restaurant_name(name):
        return None
    card = _restaurant_card(name, city or city_hint, guide, level, cuisine, price, "", address, raw=text)
    return card if _premium_city_matches(card, city_hint) else None

def _extract_black_pearl_heading_cards(chunk: str, query: str, guide: str, city_hint: str) -> list[dict]:
    text = unicodedata.normalize("NFKC", str(chunk or "")).translate(_BLACK_PEARL_CHAR_MAP)
    text = re.sub(r"[ \t]+", " ", text)
    lines = [_premium_clean_line(x) for x in re.split(r"\n+| / ", text) if _premium_clean_line(x)]
    cards = []
    section_city_m = re.search(r"([\u4e00-\u9fff]{1,8})\s*[-—－]\s*黑珍珠", text)
    city = _city_alias(section_city_m.group(1)) if section_city_m else (city_hint or _premium_query_city_scope(query, "")[0])
    current_name = ""
    block = []
    def flush():
        nonlocal current_name, block
        if not current_name or not block:
            current_name, block = "", []
            return
        raw = " ".join(block)
        if not re.search(r"黑珍珠|餐厅定位|必点招牌|用餐体验|适合场景", raw):
            current_name, block = "", []
            return
        price = _premium_field(raw, [r"人均(?:约)?\s*([¥￥]?\s*[0-9]+[+]?元?)"])
        cuisine = ""
        for kw in ("苏帮菜", "淮扬菜", "潮州菜", "粤菜", "闽菜", "海鲜", "素食", "西餐", "法餐", "川菜", "火锅", "日料", "中餐"):
            if kw in current_name or kw in raw:
                cuisine = kw
                break
        address = _premium_field(raw, [r"用餐体验\s*[:：]\s*([^,，;；。]{4,40})"])
        reason = _premium_field(raw, [r"黑珍珠定位\s*[:：]\s*([^。；;]{4,60})", r"餐厅定位\s*[:：]\s*([^。；;]{4,60})"])
        recommended = _premium_field(raw, [r"适合场景\s*[:：]\s*([^。；;]{4,60})"])
        card = _restaurant_card(current_name, city, guide, "黑珍珠", cuisine, price, "", address, reason, recommended, raw=current_name + " " + raw)
        if _premium_city_matches(card, city):
            cards.append(card)
        current_name, block = "", []
    for line in lines:
        if re.match(r"^[\u4e00-\u9fffA-Za-z0-9·&（）() -]{2,24}$", line) and not re.search(r"为您精选|满足|需求|黑珍珠[:：]|米其林[:：]", line):
            if re.search(r"菜|餐|海鲜|素食|火锅|景观|酒店|庭院|高空|地道|标杆|代表|精选|洋房|海景|园林|创意|闽|苏帮|淮扬|粤|潮州|西餐|法餐", line):
                flush()
                current_name = line
                block = []
                continue
        if current_name:
            block.append(line)
    flush()
    return cards

def _michelin_csv_cards(query: str, city_hint: str, limit: int = 5) -> list[dict]:
    if not os.path.exists(CSV_PATH):
        return []
    q_full = _enhance_query(query)
    target_city = city_hint or _premium_query_city_scope(query, "")[0]
    city_terms = {target_city, _CITY_MAP.get(target_city, "")}
    city_terms = {c.lower() for c in city_terms if c}
    rows = []
    try:
        with open(CSV_PATH, "r", encoding="utf-8") as f:
            for row in csv.DictReader(f):
                location = " ".join([row.get("location", ""), row.get("country", ""), row.get("address", "")]).lower()
                if city_terms and not any(c in location for c in city_terms):
                    continue
                blob = " ".join(str(row.get(k, "")) for k in ("name", "cuisine", "award", "content", "location")).lower()
                score = 1
                for term in re.findall(r"[\u4e00-\u9fff]{2,}|[A-Za-z]{3,}", q_full):
                    if term.lower() in blob:
                        score += 2
                try:
                    score += int(float(row.get("star_rating") or 0)) * 3
                except Exception:
                    pass
                rows.append((score, row))
        rows.sort(key=lambda x: x[0], reverse=True)
    except Exception:
        return []
    cards = []
    for _, row in rows[:limit]:
        name = row.get("name", "")
        if not _looks_restaurant_name(name):
            continue
        level = row.get("award") or (f"{row.get('star_rating')}星" if row.get("star_rating") else "")
        card = _restaurant_card(
            name=name,
            city=target_city or row.get("location", ""),
            guide="Michelin",
            level=level,
            cuisine=row.get("cuisine", ""),
            avg_price=row.get("price", ""),
            area=row.get("location", ""),
            address=row.get("address", ""),
            reason=f"{level or '入选餐厅'}，适合高端餐饮参考。",
            recommended_for="高端聚餐 / 旅行餐厅 / 纪念日",
            raw=json.dumps({k: row.get(k, "") for k in ("name", "location", "award", "cuisine")}, ensure_ascii=False),
        )
        if _premium_city_matches(card, target_city):
            cards.append(card)
    return cards

def _cards_from_nearest_result(nearest_result: dict, city_hint: str = "") -> list[dict]:
    cards = []
    if not (nearest_result and nearest_result.get("success")):
        return cards
    for r in nearest_result.get("restaurants", [])[:5]:
        if not isinstance(r, dict) or not _looks_restaurant_name(r.get("name", "")):
            continue
        note = f"距当前位置约{r.get('distance_km')}km。" if r.get("distance_km") is not None else ""
        cards.append(_restaurant_card(
            name=r.get("name", ""),
            city=city_hint or r.get("location", ""),
            guide="Michelin",
            level=r.get("award") or (f"{r.get('star_rating')}星" if r.get("star_rating") else ""),
            cuisine=r.get("cuisine", ""),
            avg_price=r.get("price", ""),
            area=r.get("location", ""),
            address=r.get("address", ""),
            reason=note or "按当前位置距离排序。",
            recommended_for="就近高端餐饮 / 旅行餐厅",
            raw=json.dumps(r, ensure_ascii=False),
        ))
    return cards

def extract_restaurant_cards(raw_chunks: list[str], query: str, guide: str = "Restaurant Guide",
                             city: str = "") -> list[dict]:
    target_city = city or _premium_query_city_scope(query, "")[0]
    cards = []
    seen = set()
    def add(card: dict | None):
        if not card:
            return
        if target_city and not card.get("city"):
            card["city"] = target_city
        if target_city and not _premium_city_matches(card, target_city):
            return
        name = _premium_clean_line(card.get("name", ""))
        if not _looks_restaurant_name(name) or name in seen:
            return
        seen.add(name)
        card.pop("_raw", None)
        cards.append(card)
    for chunk in raw_chunks or []:
        text = str(chunk or "")
        g = _premium_guide_label(text + " " + query, guide)
        if "黑珍珠" in text:
            for card in _extract_black_pearl_heading_cards(text, query, "BlackPearl", target_city):
                add(card)
        pieces = []
        for line in re.split(r"\n+|(?=\s*\d+\s*[.、)]\s*\[?\d*\]?)", text):
            clean = _premium_clean_line(line)
            if clean:
                pieces.append(clean)
        for line in pieces:
            add(_extract_pipe_restaurant(line, query, g, target_city))
            if len(cards) >= 8:
                break
        if len(cards) >= 8:
            break
    if _looks_michelin_intent(query) and len(cards) < 3:
        for card in _michelin_csv_cards(query, target_city, limit=5):
            add(card)
    return cards[:8]

def _build_restaurant_recommendations_response(query: str, city: str, sections: list[dict],
                                               nearest_result: dict = None) -> dict:
    query_city, explicit = _premium_query_city_scope(query, city)
    target_city = query_city or _premium_non_default_city(city, query)
    restaurants = []
    seen = set()
    if not target_city:
        hit_chunks = sum(int(s.get("chunk_count") or 0) for s in sections or [])
        return {
            "success": False,
            "reply_type": "restaurant_recommendations",
            "title": "餐厅推荐",
            "city": "",
            "summary": "请先确认城市或授权定位，我再按对应城市整理榜单餐厅。",
            "restaurants": [],
            "actions": [
                {"label": "使用当前位置", "action_type": "retry_with_location", "payload": {"query": query}, "requires_confirm": False},
                {"label": "手动填写城市", "action_type": "ask_city", "payload": {"query": query}, "requires_confirm": False},
            ],
            "tech_meta": {
                "restaurant_lookup": "blocked",
                "chunk_count": hit_chunks,
                "extraction_status": "city_required",
                "files": [s.get("source_label") for s in sections or [] if s.get("source_label")],
            },
        }
    def add_cards(cards):
        for card in cards or []:
            name = _premium_clean_line(card.get("name", ""))
            if not _looks_restaurant_name(name) or name in seen:
                continue
            if target_city and not card.get("city"):
                card["city"] = target_city
            if target_city and not _premium_city_matches(card, target_city):
                continue
            seen.add(name)
            restaurants.append(card)
    add_cards(_cards_from_nearest_result(nearest_result, target_city))
    for section in sections or []:
        raw_chunks = section.get("_raw_chunks") or []
        guide = section.get("guide") or _premium_guide_label(section.get("title", ""))
        add_cards(extract_restaurant_cards(raw_chunks, query, guide, target_city))
    hit_chunks = sum(int(s.get("chunk_count") or 0) for s in sections or [])
    if restaurants:
        summary = "根据榜单餐厅资料整理，营业状态和订位需二次确认。"
        if not explicit and target_city:
            summary = f"按当前城市「{target_city}」整理，营业状态和订位需二次确认。"
        return {
            "success": True,
            "reply_type": "restaurant_recommendations",
            "title": "餐厅推荐",
            "city": target_city,
            "summary": summary,
            "restaurants": restaurants[:6],
            "actions": [
                {"label": "加入行程", "action_type": "add_restaurant_to_plan", "payload": {}, "requires_confirm": False},
                {"label": "生成 Mock 订位", "action_type": "restaurant_confirm", "payload": {}, "requires_confirm": True},
                {"label": "换一家", "action_type": "replace_restaurant", "payload": {}, "requires_confirm": False},
            ],
            "tech_meta": {
                "restaurant_lookup": "hit" if hit_chunks else "empty",
                "chunk_count": hit_chunks,
                "extraction_status": "success",
                "files": [s.get("source_label") for s in sections or [] if s.get("source_label")],
            },
        }
    return {
        "success": False,
        "reply_type": "restaurant_recommendations",
        "title": "餐厅推荐",
        "city": target_city,
        "summary": "我检索到了相关餐厅资料，但暂时没有识别出明确餐厅名。可以换一个城市或关键词重新查。",
        "restaurants": [],
        "actions": [
            {"label": "重新检索", "action_type": "retry_restaurant_search", "payload": {"query": query}, "requires_confirm": False},
            {"label": "换成美团搜索", "action_type": "call_meituan_skill", "payload": {"intent": "restaurant_search", "city": target_city, "keyword": "餐厅"}, "requires_confirm": False},
            {"label": "查看技术详情", "action_type": "show_tech_detail", "payload": {}, "requires_confirm": False},
        ],
        "tech_meta": {
            "restaurant_lookup": "hit" if hit_chunks else "empty",
            "chunk_count": hit_chunks,
            "extraction_status": "failed",
            "files": [s.get("source_label") for s in sections or [] if s.get("source_label")],
        },
    }

def _premium_visible_text(text: str) -> str:
    return _premium_user_safe_text(text)

def _premium_section(title: str, result: dict, source_label: str) -> dict:
    raw_chunks = _premium_raw_chunks(result)
    return {
        "title": "黑珍珠推荐" if "黑珍珠" in title else ("米其林推荐" if "米其林" in title else "餐厅推荐"),
        "guide": _premium_guide_label(title),
        "success": bool(result.get("success")),
        "answer": _premium_visible_text(result.get("answer", "")),
        "source_label": source_label,
        "fallback": bool(result.get("fallback", False)),
        "vector_rag": bool(result.get("vector_rag", False)),
        "error": _premium_visible_text(result.get("error", "")),
        "chunk_count": len(raw_chunks),
        "_raw_chunks": raw_chunks,
    }


def _premium_black_pearl_query(query: str) -> str:
    cleaned = re.sub(r"米其林|michelin|一星|二星|三星|摘星", " ", str(query or ""), flags=re.I)
    cleaned = re.sub(r"\s+", " ", cleaned).strip()
    return cleaned if _looks_black_pearl_intent(cleaned) else f"{cleaned} 黑珍珠".strip()


def _premium_michelin_query(query: str) -> str:
    cleaned = re.sub(r"黑珍珠|black\s*pearl", " ", str(query or ""), flags=re.I)
    cleaned = re.sub(r"\s+", " ", cleaned).strip()
    return cleaned if _looks_michelin_intent(cleaned) else f"{cleaned} 米其林".strip()


def tool_search_local_michelin_rag(query: str) -> dict:
    """Use the local hei_zhen_zhu_local.py RAG for Michelin data before any heavy model path."""
    try:
        from hei_zhen_zhu_local import query_michelin_black_pearl
        rag_result = query_michelin_black_pearl(_premium_michelin_query(query))
        answer = _clean_markdown(rag_result.get("answer", ""))
        hits = rag_result.get("hits") or []
        if answer and hits:
            return {
                "success": True,
                "answer": answer,
                "references": rag_result.get("references", [os.path.basename(CSV_PATH)]),
                "source": CSV_PATH,
                "contexts": [h.get("text", "") for h in hits if isinstance(h, dict)],
                "structured": rag_result.get("structured", {}),
                "vector_rag": True,
            }
    except Exception as e:
        print(f"[MICHELIN_LOCAL_RAG_FALLBACK] {_safe_error_text(e)}")
    return tool_search_michelin(query)


def tool_search_premium_dining(query: str, city: str = "") -> dict:
    """Query local Michelin / Black Pearl RAG data. Never returns mock data."""
    query = str(query or "").strip()
    city = str(city or "").strip()
    cache_payload = {"query": query, "city": city}
    cached = _external_cache_get("rag", cache_payload)
    if cached is not None:
        return cached
    if _external_circuit_open("rag"):
        return {
            "success": False,
            "reply_type": "restaurant_recommendations",
            "title": "餐厅推荐",
            "city": city,
            "summary": "餐厅资料暂未返回，稍后可以换城市或关键词再查。",
            "restaurants": [],
            "actions": [
                {"label": "重新检索", "action_type": "retry_restaurant_search", "payload": {"query": query}, "requires_confirm": False},
                {"label": "换成美团搜索", "action_type": "call_meituan_skill", "payload": {"intent": "restaurant_search", "city": city, "keyword": "餐厅"}, "requires_confirm": False},
            ],
            "message": FRIENDLY_BACKUP_MESSAGE,
            "uses_mock": False,
        }
    query_city, explicit_city = _premium_query_city_scope(query, city)
    city = query_city or _premium_non_default_city(city, query)
    full_query = query
    if city and not explicit_city and city not in full_query:
        full_query = f"{city} {full_query}".strip()

    wants_black_pearl = _looks_black_pearl_intent(full_query)
    wants_michelin = _looks_michelin_intent(full_query)
    if _looks_generic_premium_dining(full_query) and not (wants_black_pearl or wants_michelin):
        wants_black_pearl = True
        wants_michelin = True
    if not (wants_black_pearl or wants_michelin):
        wants_black_pearl = True
        wants_michelin = True

    print(f"[PREMIUM_DINING_RAG] city={city or '-'} query={full_query}")
    sections = []
    if wants_black_pearl:
        bp_query = _premium_black_pearl_query(full_query)
        bp_result = tool_search_black_pearl(bp_query)
        bp_source = (
            f"{os.path.basename(BLACK_PEARL_SINGAPORE_XLSX_PATH)} / {os.path.basename(BLACK_PEARL_PDF_PATH)}"
            if re.search(r"新加坡|singapore", bp_query, re.I)
            else os.path.basename(BLACK_PEARL_PDF_PATH)
        )
        sections.append(_premium_section("黑珍珠知识库", bp_result, bp_source))
    if wants_michelin:
        michelin_query = _premium_michelin_query(full_query)
        michelin_result = tool_search_local_michelin_rag(michelin_query)
        sections.append(_premium_section("米其林知识库", michelin_result, os.path.basename(CSV_PATH)))

    response = _build_restaurant_recommendations_response(full_query, city, sections)
    success = bool(response.get("success"))
    public_sections = [
        {k: v for k, v in s.items() if k not in ("_raw_chunks", "answer", "error")}
        for s in sections
    ]
    response.update({
        "mode": "premium_dining_rag",
        "query": full_query,
        "city": city,
        "uses_mock": False,
        "message": "已整理出餐厅推荐，未使用 Mock 数据。" if success else response.get("summary", "暂未识别出明确餐厅名。"),
        "local_sources": {
            "black_pearl_non_singapore_pdf": os.path.basename(BLACK_PEARL_PDF_PATH),
            "black_pearl_singapore_xlsx": os.path.basename(BLACK_PEARL_SINGAPORE_XLSX_PATH),
            "michelin_csv": os.path.basename(CSV_PATH),
        },
        "sections": public_sections,
    })
    _external_cache_set("rag", cache_payload, response)
    _external_circuit_record("rag", bool(response.get("success")), response.get("message") or response.get("summary"))
    return response


def _premium_dining_final_text(result: dict, nearest_result: dict = None) -> str:
    payload = _build_restaurant_recommendations_response(
        result.get("query") or result.get("message") or "",
        result.get("city") or "",
        result.get("sections", []),
        nearest_result,
    )
    return json.dumps(payload, ensure_ascii=False)


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
    cache_payload = {
        "intent": intent,
        "city": city,
        "keyword": search_kw,
        "location": location or "",
        "lat": round(float(user_lat), 5) if user_lat else "",
        "lng": round(float(user_lng), 5) if user_lng else "",
        "filters": filters,
        "limit": int(limit or 5),
    }
    cached = _external_cache_get("meituan", cache_payload)
    if cached:
        return cached
    if _external_circuit_open("meituan"):
        return {
            "success": False,
            "intent": intent,
            "city": city,
            "keyword": search_kw,
            "source": "meituan_skill",
            "is_real_meituan": False,
            "error": MEITUAN_REAL_FRIENDLY_FALLBACK,
            "message": MEITUAN_REAL_FRIENDLY_FALLBACK,
            "mock_notice": "Mock 演示数据，非真实商户，仅用于黑客松端到端演示。",
        }
    skill_route = _pick_meituan_skill(intent, search_kw)
    t0 = time.perf_counter()

    def finish(result: dict) -> dict:
        elapsed = round((time.perf_counter() - t0) * 1000)
        result = result or {}
        result.setdefault("elapsed_ms", elapsed)
        status = "success" if result.get("success") else ("timeout" if "超时" in str(result.get("error", "")) else "error")
        _record_tool_call("meituan_skill", status, elapsed, city=city, intent=intent, source=result.get("source", ""))
        if result.get("success"):
            _external_cache_set("meituan", cache_payload, result)
            _external_circuit_record("meituan", True)
        else:
            result["error"] = MEITUAN_REAL_FRIENDLY_FALLBACK
            result["message"] = MEITUAN_REAL_FRIENDLY_FALLBACK
            result["mock_notice"] = "Mock 演示数据，非真实商户，仅用于黑客松端到端演示。"
            _external_circuit_record("meituan", False, result.get("detail") or status)
        return result

    if skill_route == "coupon":
        return finish(_apply_city_guard_to_result(_call_meituan_coupon_skill(intent, city, search_kw, limit), city))
    if skill_route == "paotui":
        return finish(_apply_city_guard_to_result(_call_meituan_paotui_skill(intent, city, search_kw, user_lat, user_lng, limit), city))
    if skill_route == "venue":
        venue_result = _call_meituan_venue_skill(intent, city, search_kw, limit)
        if venue_result.get("success"):
            return finish(_apply_city_guard_to_result(venue_result, city))
        cli_fallback = _call_meituan_travel_cli(intent, city, search_kw, filters, limit)
        if cli_fallback.get("success"):
            cli_fallback["detail"] = "venue skill unavailable; used mttravel skill"
            return finish(_apply_city_guard_to_result(cli_fallback, city))
        return finish(venue_result)

    # ══ Layer1：美团开放平台（需在 open.meituan.com 申请） ══
    if MEITUAN_API_KEY:
        try:
            import hashlib
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
                return finish(_apply_city_guard_to_result({"success":True,"intent":intent,"city":city,
                        "keyword":search_kw,"count":len(results),
                        "results":results,"source":"meituan_skill",
                        "is_real_meituan": True}, city))
        except Exception as e:
            print(f"[meituan_api] {_safe_error_text(e)}，降级到本地美团 Skill")

    # ══ Layer2：本地美团 Travel Skill CLI（mttravel） ══
    cli_result = _call_meituan_travel_cli(intent, city, search_kw, filters, limit)
    if cli_result.get("success"):
        return finish(_apply_city_guard_to_result(cli_result, city))

    return finish({
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
    })


def _tool_summary(fn: str, args: dict, result: dict) -> str:
    if not result.get("success"):
        return f"⚠️ {_friendly_external_error(result.get('message') or result.get('error') or FRIENDLY_BACKUP_MESSAGE)}"
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
            return f"⚠️ {_friendly_external_error(result.get('message') or result.get('error') or FRIENDLY_BACKUP_MESSAGE)}"
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
    if fn=="search_black_pearl":
        ans=_clean_markdown(result.get("answer",""))
        return ans[:100]+"…" if len(ans)>100 else ans
    if fn=="call_meituan_skill":
        if not result.get("success"):
            return f"⚠️ {_friendly_external_error(result.get('message') or result.get('error') or MEITUAN_REAL_FRIENDLY_FALLBACK)}"
        if result.get("fallback") or result.get("source") == "mock_fallback":
            return f"美团 Skill 暂不可用，未展示店名：{result.get('city','')}{result.get('keyword','')}"
        count = result.get("count", 0)
        kw    = result.get("keyword", "")
        city  = result.get("city", "")
        tops  = result.get("results", [])[:2]
        names = "、".join([r["name"] for r in tops if r.get("name")])
        return f"🍴 {city}{kw}：找到{count}家，推荐：{names}"
    if fn=="longcat_resource_search":
        if not result.get("success"):
            return result.get("message") or "美团龙猫暂不可用，已切换备用数据源"
        kws = result.get("keywords") or {}
        flat = []
        for v in kws.values():
            if isinstance(v, list):
                flat.extend([str(x) for x in v[:2]])
        return f"美团龙猫资源搜索：{result.get('city','')} · {'、'.join(flat[:5]) or '资源策略已生成'}"
    if fn=="amap_poi":
        if not result.get("success"):
            return result.get("message") or "⚠️ 地图路线暂未返回，已启用备用方案"
        names = "、".join([x.get("name","") for x in (result.get("results") or [])[:3] if x.get("name")])
        return f"地图参考：{result.get('city','')}{result.get('keyword','')} · 找到{result.get('count',0)}个 · {names}"
    if fn=="amap_route":
        if not result.get("success"):
            return result.get("message") or "⚠️ 地图路线暂未返回，已启用备用方案"
        dist = round((result.get("distance_m") or 0) / 1000, 1)
        mins = max(1, round((result.get("duration_sec") or 0) / 60)) if result.get("duration_sec") else "-"
        return f"地图路线规划：{' → '.join(result.get('waypoints') or [])} · {dist}km · {mins}min"
    if fn=="amap_map_link":
        return "地图链接生成完成" if result.get("success") else "地图链接生成失败"
    if fn=="amap_travel_planner":
        if not result.get("success"):
            return result.get("message") or result.get("error") or "⚠️ 地图路线暂未返回，已启用备用方案"
        return f"地图智能规划：{len(result.get('pois') or [])}个地点 · {round((result.get('distance_m') or 0)/1000,1)}km"
    if fn=="public_facility_search":
        if not result.get("success"):
            return result.get("message") or "请开启定位后再查询附近卫生间"
        names = "、".join([x.get("name","") for x in (result.get("results") or [])[:3] if x.get("name")])
        return f"附近卫生间查询：找到{result.get('count',0)}个可尝试地点 · {names}"
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
        n=len(result.get("flights",[]))
        return f"Mock 航班：{result.get('origin','')} → {result.get('destination','')} · {n}个候选 · 推荐 {rec.get('flight_no','')} ¥{rec.get('price','-')}"
    if fn=="mock_book_train":
        t=result.get("train",{})
        oid=result.get("order",{}).get("order_id","")
        return f"高铁待确认：{t.get('train_no','')} {t.get('seat_class','')} · {t.get('depart_time','')} · ¥{t.get('price','-')} · 订单 {oid}"
    if fn=="mock_book_resource":
        m=result.get("merchant",{})
        oid=result.get("order",{}).get("order_id","")
        cat=result.get("order",{}).get("item",{}).get("category","资源")
        return f"{cat}待确认：{m.get('name','')} · ¥{m.get('price','-')} · 评分{m.get('rating','-')} · 订单 {oid}"
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
            "用户明确提到黑珍珠时应调用 search_black_pearl。"
            "不得凭记忆回答，必须查库。"
        ),
        "parameters":{"type":"object","properties":{
            "query":{"type":"string","description":"查询内容，支持中英文"}},"required":["query"]}}},
    {"type":"function","function":{
        "name":"search_black_pearl",
        "description":(
            "【必须调用】查询本地《黑珍珠-米其林.pdf》。"
            "用户提到黑珍珠、黑珍珠餐厅、黑珍珠榜单、黑珍珠/米其林PDF、高端餐饮榜单时必须调用。"
            "检索内容必须来自项目根目录的 黑珍珠-米其林.pdf，不得凭记忆回答。"
        ),
        "parameters":{"type":"object","properties":{
            "query":{"type":"string","description":"查询内容，支持城市、菜系、预算、人均价格等"}},"required":["query"]}}},
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
        "description":"本地 Mock 航班查询，返回模拟航班列表（不跳转任何外部网站）。用户说机票、航班、飞机票、订机票、买机票时必须调用。仅用于演示，不代表真实出票。",
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
        "name":"mock_book_train",
        "description":"查询高铁/火车并生成高铁票待确认订单。用户说高铁、火车票、动车、订高铁票、买高铁票时必须调用。只生成待确认订单，确认后商家与用户同时收到预定，不真实出票。",
        "parameters":{"type":"object","properties":{
            "origin":{"type":"string","description":"出发城市/车站"},
            "destination":{"type":"string","description":"到达城市/车站"},
            "date":{"type":"string","description":"乘车日期，可为空"},
            "seat_class":{"type":"string","description":"席别：二等座/一等座/商务座，默认二等座"},
            "passengers":{"type":"integer","description":"乘车人数，默认1"},
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
2. 高德地图 / 百度地图 API：用于 POI 搜索、地理编码、路线规划、距离和通勤时间估算；地图优先级为高德优先，百度备用。
3. 美团 Skill / 米其林知识库 / Mock 数据：用于餐饮、酒店、排队、下单等本地生活资源演示。

你必须采用「真实工具结果优先 + DeepSeek 结构化规划 + 可信兜底」的规划模式。

你的目标不是聊天，而是帮用户把一次短途出游任务尽可能完整地做完：
理解需求、补全默认假设、调用地图能力、生成可执行路线、安排吃喝玩乐、控制预算、处理异常、生成待确认动作。

## 工具调用优先级

1. 吃喝玩乐 / 周边游 / 城市规划：
   DeepSeek 意图解析 → 美团龙猫资源搜索 → 美团 Skill 搜餐饮/酒店/景点/团购 → 高德 POI 补充坐标 → 高德路线规划 → DeepSeek 生成 route_map_json → Mock 排队/打车/订单 → 前端渲染路线卡。
2. 找酒店 / 餐厅 / 景点：
   城市解析 → 美团龙猫 / 美团 Skill → 高德 POI → Mock 兜底 → DeepSeek 总结推荐。
3. 路线 / 怎么走 / 地图：
   高德路线规划 → 高德地图链接 → DeepSeek 总结路线 → 前端地图卡。除非用户还提到吃饭、酒店、门票，否则不要先调美团。
4. 高端餐厅 / 米其林 / 黑珍珠 / 纪念日：
   米其林/黑珍珠知识库 → 美团资源 → 高德 POI → DeepSeek 推荐。
5. 订酒店 / 打车 / 买票 / 下单：
   先搜索真实资源 → 高德校验位置/路线 → 生成待确认订单 → 用户确认 → Mock 下单成功。

## 输出结构铁律

用户提出出游需求后，必须按以下顺序组织结果：
1. 一句话摘要
2. route_map_json 路线地图卡
3. 关键指标
4. 时间线详情
5. 美团/龙猫资源推荐
6. 预算拆分
7. 风险和异常兜底
8. 待确认动作

禁止默认调用航班、默认调用酒店、默认骑行、输出模板路线、展示其他城市结果，或用当前位置覆盖用户明确城市。

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

## 新任务处理规则

你是一个持续任务型出游 Agent。

如果用户只是说：
"重新开始""清空""重置""换个话题"
你可以清空当前任务，并等待新需求。

但如果用户在同一句话里已经给出新目的地或新需求，例如：
"我想去泉州玩，请你做规划"
"我想去厦门"
"帮我规划杭州2天"
"周末去桂林玩"
"从上海去苏州玩一天"

你必须理解为：
清空旧任务 + 立即创建新任务 + 立即生成规划。

禁止回复：
"已重置当前任务，请告诉我新的需求"

因为用户已经告诉了新需求。

本轮用户明确提到的目的地拥有最高优先级，不能被历史城市或默认城市覆盖。

三、真实地图使用规则

你必须优先利用高德地图能力处理，百度地图作为备用：
1. 起点和终点地理解析。
2. 城市之间或城市内的距离判断。
3. 路线交通方式建议。
4. 点位之间交通时间估算。
5. 是否跨城。
6. 是否适合步行 / 打车 / 公共交通；骑行只在用户明确提出时启用。

当高德/百度地图返回真实路线、距离或时间时：
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

每条路线至少包含 3 个节点，节点必须写成自然可执行的地点或片区名，例如"青秀山上午慢游""三街两巷午餐+citywalk""中山路夜市收尾"。
节点可以是：
- 交通节点
- 景点
- 餐饮
- 咖啡/休息
- 夜景
- 商圈
- 酒店

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
- 数据来源：高德 / 百度 / 美团 / 米其林知识库 / area_suggestion / Mock 示例

## 路线卡生成铁律

你必须根据工具结果生成 route_map_json，让前端渲染路线地图卡。

禁止输出模板化路线卡标题，包括：
- 代表性景区区域
- 核心商圈餐饮区域
- 历史文化街区
- 夜游/滨水区域
- 区域建议开场
- 景点·XX区域
- 餐饮·XX区域

如果高德 MCP / 高德 Skill / 美团 Skill 返回了真实 POI，必须优先使用真实 POI。

如果没有真实 POI，也要基于城市常识生成自然可执行路线节点，例如：
"青秀山上午慢游"
"三街两巷午餐+citywalk"
"中山路夜市收尾"
而不是"代表性景区区域"。

每个 route_map 节点必须包含：
- step
- name
- type
- arrival_time
- stay_minutes
- short_desc
- next_transport
- next_duration_minutes
- estimated_cost
- data_source
- is_real_poi
- need_verify
- risk

输出必须优先包含 JSON：
{
  "answer_type": "trip_plan",
  "city": "",
  "title": "",
  "summary": "",
  "route_map": [],
  "metrics": {},
  "budget": {},
  "actions": []
}

前端将使用 route_map 渲染地图卡，所以 route_map 必须稳定、完整、可执行。

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
  "answer_type": "trip_plan",
  "city": "",
  "title": "",
  "summary": "",
  "route_map": [
    {
      "step": 1,
      "name": "",
      "type": "",
      "arrival_time": "",
      "short_desc": "",
      "stay_minutes": 0,
      "next_transport": "",
      "next_duration_minutes": 0,
      "estimated_cost": 0,
      "data_source": "",
      "is_real_poi": false,
      "need_verify": false,
      "can_order": false,
      "risk": ""
    }
  ],
  "metrics": {
    "total_duration_minutes": 0,
    "budget_per_person": 0,
    "route_intensity": "",
    "queue_risk": "",
    "data_confidence": ""
  },
  "budget": {
    "transport": 0,
    "food": 0,
    "activity": 0,
    "hotel": 0,
    "buffer": 0
  },
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
    if plan.get("route_card_error"):
        return _clean_markdown(plan.get("route_card_error") or "路线生成失败，请重试")
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

_ROUTE_JSON_CACHE = {}  # key -> (ts, route_card)；同一城市+需求 30 分钟内复用，演示重复 prompt 秒出
_ROUTE_JSON_TTL = int(os.environ.get("ROUTE_JSON_CACHE_TTL", "1800"))

def _route_json_cache_key(user_message: str, tool_context: dict) -> str:
    city = (tool_context or {}).get("city") or ""
    budget = (tool_context.get("budget") or {}).get("total") if isinstance((tool_context or {}).get("budget"), dict) else ""
    base = f"{city}|{budget}|{str(user_message or '').strip()}"
    return hashlib.md5(base.encode("utf-8")).hexdigest()

def _compact_route_resource_items(items: list, limit: int = 8) -> list:
    compact = []
    for item in (items or [])[:limit]:
        if not isinstance(item, dict):
            continue
        compact.append({
            "name": item.get("name") or item.get("title") or "",
            "type": item.get("type") or item.get("category") or item.get("intent") or "",
            "address": item.get("address") or "",
            "rating": item.get("rating") or item.get("score") or "",
            "avg_price": item.get("avg_price") or item.get("cost") or item.get("price") or "",
            "lat": item.get("lat") or item.get("latitude") or "",
            "lng": item.get("lng") or item.get("longitude") or "",
            "data_source": item.get("data_source") or item.get("source") or "",
            "is_real_poi": bool(item.get("is_real_poi") or item.get("is_real_meituan") or _is_real_map_poi_item(item)),
        })
    return compact

def _route_item_from_tool(item: dict, source_type: str, display_source: str) -> dict:
    return {
        "name": item.get("name") or item.get("title") or "",
        "type": item.get("type") or item.get("category") or source_type,
        "city": item.get("city") or "",
        "address": item.get("address") or "",
        "rating": item.get("rating") or item.get("score") or "",
        "price": item.get("avg_price") or item.get("cost") or item.get("price") or "",
        "opening_hours": item.get("opening_hours") or item.get("business_hours") or "",
        "lat": item.get("lat") or item.get("latitude") or "",
        "lng": item.get("lng") or item.get("longitude") or "",
        "source_type": source_type,
        "display_source": display_source,
    }

def _is_usable_route_tool_item(item: dict, city: str = "") -> bool:
    if not isinstance(item, dict) or not str(item.get("name") or item.get("title") or "").strip():
        return False
    if item.get("fallback") or item.get("is_area_suggestion") or item.get("source") == "mock_fallback":
        return False
    if item.get("data_level") == "C_MOCK_REGION":
        return False
    item_city = _city_alias(str(item.get("city") or ""))
    want_city = _city_alias(city or "")
    if item_city and want_city and item_city != want_city and not (want_city == "福鼎" and item_city == "宁德") and not (want_city == "宁德" and item_city == "福鼎"):
        return False
    lat = _coerce_float(item.get("lat") or item.get("latitude"))
    lng = _coerce_float(item.get("lng") or item.get("longitude"))
    if lat is not None and lng is not None and city and not _coord_within_city(lat, lng, city):
        return False
    return bool(_is_real_meituan_item(item) or _is_real_map_poi_item(item) or item.get("source_type") in ("restaurant", "hotel", "group_buy", "local_life", "map_route", "attraction"))

def _route_tool_payload(user_message: str, tool_context: dict) -> dict:
    ctx = tool_context or {}
    req = ctx.get("requirements") if isinstance(ctx.get("requirements"), dict) else {}
    budget = ctx.get("budget") if isinstance(ctx.get("budget"), dict) else {}
    persona = ctx.get("persona") if isinstance(ctx.get("persona"), dict) else {}
    city = _guard_city_name(ctx.get("city") or req.get("destination") or "")
    pool = ctx.get("candidate_pool") if isinstance(ctx.get("candidate_pool"), dict) else {}
    raw_hotels = pool.get("hotels") if pool else ctx.get("meituan_hotels")
    raw_restaurants = pool.get("restaurants") if pool else ctx.get("meituan_restaurants")
    raw_spots = pool.get("spots") if pool else ctx.get("meituan_spots")
    raw_map_pois = [] if pool else ctx.get("amap_pois")
    raw_hotels = city_guard_for_candidates(raw_hotels or [], city, "payload_hotels")
    raw_restaurants = city_guard_for_candidates(raw_restaurants or [], city, "payload_restaurants")
    raw_spots = city_guard_for_candidates(raw_spots or [], city, "payload_spots")
    raw_map_pois = city_guard_for_candidates(raw_map_pois or [], city, "payload_map_pois")
    hotels = [_route_item_from_tool(x, "hotel", "酒店数据") for x in raw_hotels if _is_usable_route_tool_item(x, city)][:5]
    restaurants = [_route_item_from_tool(x, "restaurant", "餐厅数据") for x in raw_restaurants if _is_usable_route_tool_item(x, city)][:5]
    local_life = [_route_item_from_tool(x, "local_life", "本地生活数据") for x in raw_spots if _is_usable_route_tool_item(x, city)][:8]
    map_pois = [_route_item_from_tool(x, "map_route", "地图数据") for x in raw_map_pois if _is_usable_route_tool_item(x, city)][:8]
    candidate_pool = []
    seen = set()
    for item in (local_life + restaurants + hotels + map_pois):
        name = _norm_place_name(item.get("name") or "")
        if not name or name in seen:
            continue
        seen.add(name)
        candidate_pool.append(item)
        if len(candidate_pool) >= 24:
            break
    return {
        "user_input": user_message,
        "parsed_info": {
            "destination": city,
            "origin": req.get("origin") or "",
            "days": req.get("days") or 1,
            "persona": "、".join(persona.get("labels") or persona.get("keys") or []),
            "theme": "",
            "budget": budget.get("total") or req.get("budget") or "",
        },
        "tool_result": {
            "michelin_rag_result": [],
            "black_pearl_rag_result": [],
            "meituan_skill_result": {
                "hotels": hotels,
                "restaurants": restaurants,
                "group_buys": [],
                "local_life": local_life,
            },
            "amap_skill_result": {
                "route_order": [x["name"] for x in map_pois if x.get("name")],
                "distance_notes": [],
                "transport_suggestions": [],
                "pois": map_pois,
            },
        },
        "candidate_pool": {
            "target_city": city,
            "spots": local_life,
            "restaurants": restaurants,
            "hotels": hotels,
            "map_pois": map_pois,
            "source_status": (pool.get("source_status") if pool else {}) or {},
        },
        "allowed_place_names": [x["name"] for x in candidate_pool if x.get("name")],
        "weather": ctx.get("weather") or {},
        "budget": budget,
    }

def _strict_insufficient_route(destination: str, budget: dict = None) -> dict:
    budget = budget if isinstance(budget, dict) else {}
    return {
        "answer_type": "trip_plan",
        "destination": destination or "目的地",
        "city": destination or "目的地",
        "data_status": "insufficient",
        "title": "暂无法生成可靠路线",
        "route_title": "暂无法生成可靠路线",
        "summary": "真实地点数据不足，不强行生成。",
        "route_map": [],
        "route_items": [],
        "metrics": {
            "total_budget": budget.get("total"),
            "budget_per_person": budget.get("total"),
            "route_intensity": "--",
            "queue_risk": "真实地点不足",
            "data_confidence": "insufficient",
        },
        "budget": budget,
        "warnings": ["未检索到足够真实地点", "建议扩大搜索范围"],
        "next_actions": ["重新搜索景点", "重新搜索酒店", "重新搜索团购"],
        "tips": ["为了避免生成虚假地点，本次不强行推荐路线。"],
        "actions": [],
    }

_DINING_TYPE_RE = re.compile(r"餐饮|餐厅|美食|小吃|火锅|烧烤|咖啡|茶饮|甜品|快餐|dining|restaurant|group_buy|local_life", re.I)
_NONDINING_TYPE_RE = re.compile(r"风景|景点|公园|博物|旅游|娱乐|购物|广场|景区|地标|寺|祠|塔|公园|古镇|街区|hotel|酒店|spot|street|park|museum|landmark", re.I)
_DINING_NAME_RE = re.compile(r"餐厅|饭店|菜馆|小吃|火锅|烧烤|海鲜|咖啡|茶馆|面馆|食堂|酒楼|餐吧|美食|烘焙|甜品|大排档|私房菜|烤肉|料理|食府|菜(?:[（(]|馆|·|$)")

def _is_dining_candidate(item: dict) -> bool:
    t = str(item.get("type") or item.get("source_type") or item.get("data_source") or "")
    if _DINING_TYPE_RE.search(t):
        return True
    if _NONDINING_TYPE_RE.search(t):
        return False
    return bool(_DINING_NAME_RE.search(str(item.get("name") or "")))

def _user_wants_food_route(user_message: str) -> bool:
    return bool(re.search(r"就想吃|美食路线|探店|吃喝为主|美食脑袋|只要餐厅|只想吃|觅食|美食游", str(user_message or "")))

def validate_route_quality(route_map: list, food_route: bool = False) -> tuple:
    """路线质量校验：非美食路线不允许全是餐饮/餐饮>2/非餐饮<2/连续3个餐饮/模板词。"""
    if not isinstance(route_map, list) or len(route_map) < 3:
        return False, "节点不足"
    names = [str(n.get("name") or "").strip() for n in route_map]
    if any(not n for n in names):
        return False, "存在空节点"
    dining = [n for n in route_map if _is_dining_candidate(n)]
    nondining = [n for n in route_map if not _is_dining_candidate(n)]
    # 模板词
    for n in route_map:
        for fld in (n.get("name"), n.get("type"), n.get("short_desc")):
            if fld and _ROUTE_TEMPLATE_BANNED.search(str(fld)):
                return False, "命中模板词"
    if not food_route:
        if len(dining) > 2:
            return False, "餐饮节点过多"
        if len(nondining) < 2:
            return False, "非餐饮点不足"
        run = 0
        for n in route_map:
            run = run + 1 if _is_dining_candidate(n) else 0
            if run >= 3:
                return False, "连续3个餐饮"
    return True, "ok"

def validate_candidate_route_quality(route_map: list, food_route: bool = False) -> tuple:
    """候选池路线可生成 2-6 个节点，但每个节点必须来自真实候选。"""
    if not isinstance(route_map, list) or len(route_map) < 2 or len(route_map) > 6:
        return False, "节点不足"
    names = [str(n.get("name") or "").strip() for n in route_map]
    if any(not n for n in names):
        return False, "存在空节点"
    for n in route_map:
        for fld in (n.get("name"), n.get("type"), n.get("short_desc")):
            if fld and _ROUTE_TEMPLATE_BANNED.search(str(fld)):
                return False, "命中模板词"
    if not food_route:
        dining = [n for n in route_map if _is_dining_candidate(n)]
        nondining = [n for n in route_map if not _is_dining_candidate(n)]
        if len(nondining) < 1:
            return False, "缺少非餐饮点"
        if len(dining) > 2:
            return False, "餐饮节点过多"
    return True, "ok"

def _deepseek_supplement_nondining(city: str, existing_names: list, user_message: str) -> list:
    """候选点过多为餐饮时，让 DeepSeek 补 2-3 个具体可验证的非餐饮点（禁模板词）。"""
    if not _has_any_llm():
        return []
    try:
        resp = _llm_chat_completion({
            "temperature": 0.3, "max_tokens": 400,
            "response_format": {"type": "json_object"},
            "messages": [
                {"role": "system", "content": (
                    "你是本地出游路线补全器。当前候选点过多是餐饮，无法形成自然出游路线。"
                    f"请为目的地『{city}』补充 2-3 个具体、可验证的非餐饮地点（知名景点/真实街区/公园/博物馆/海边江边湖边具体点/真实商业街/城市地标）。"
                    "必须是具体名称，不能是类别或模板。禁止：代表性景区区域、核心商圈、老城慢走、本地街巷散步、午餐备选区、晚餐备选区、夜景慢逛、城市中心、热门景点区域、某某附近、备选区。"
                    "只输出 JSON：{\"additional_points\":[{\"name\":\"\",\"type\":\"spot/street/park/museum/night_view/landmark\",\"reason\":\"\",\"need_verify\":true}]}；"
                    "无法确定就返回 {\"additional_points\":[],\"reason\":\"无法确认具体非餐饮点\"}。")},
                {"role": "user", "content": f"目的地：{city}\n已有候选点：{('、'.join([str(x) for x in existing_names[:10]]) or '无')}\n用户原话：{user_message}"},
            ],
        }, purpose="nondining_supplement", timeout_seconds=8)
        data = json.loads(_clean_markdown(((resp.json().get("choices") or [{}])[0].get("message") or {}).get("content", "")) or "{}")
        out = []
        for p in (data.get("additional_points") or [])[:3]:
            name = str(p.get("name") or "").strip()
            if not name or _ROUTE_TEMPLATE_BANNED.search(name):
                continue
            out.append({"name": name, "type": p.get("type") or "spot", "source_type": "city_landmark",
                        "display_source": "地图参考", "is_real_poi": True, "need_verify": True,
                        "data_source": "needs_confirmation"})
        return out
    except Exception as e:
        print(f"[nondining_supplement] {_safe_error_text(e)}")
        return []

def _food_heavy_insufficient_route(city: str, budget: dict) -> dict:
    return {
        "answer_type": "trip_plan", "city": city, "destination": city,
        "data_status": "food_heavy_insufficient", "route_map": [],
        "title": "缺少可验证景点点位", "route_title": "缺少可验证景点点位",
        "summary": "当前找到的候选点主要是餐饮，缺少可验证的景点/街区点位。为保证路线可靠，我暂不生成路线卡。你可以补充想去的景点，或点击重新搜索非餐饮点。",
        "warnings": ["候选点以餐饮为主，缺少可验证景点/街区"],
        "next_actions": ["重新搜索景点", "手动添加地点", "只生成美食路线"],
        "budget": budget or {},
    }

def _build_real_candidate_route_card(user_message: str, tool_context: dict) -> dict:
    payload = _route_tool_payload(user_message, tool_context or {})
    parsed = payload.get("parsed_info") or {}
    city = parsed.get("destination") or (tool_context or {}).get("city") or "目的地"
    tool_result = payload.get("tool_result") or {}
    mt = tool_result.get("meituan_skill_result") or {}
    amap = tool_result.get("amap_skill_result") or {}
    req = (tool_context or {}).get("requirements") if isinstance((tool_context or {}).get("requirements"), dict) else {}
    need_hotel = bool(req.get("wants_hotel"))
    candidates = []
    for key in ("pois", "route_order"):
        items = amap.get(key) or []
        if key == "route_order":
            continue
        candidates.extend([x for x in items if isinstance(x, dict)])
    candidates.extend([x for x in (mt.get("restaurants") or []) if isinstance(x, dict)])
    candidates.extend([x for x in (mt.get("local_life") or []) if isinstance(x, dict)])
    if need_hotel or not candidates:
        candidates.extend([x for x in (mt.get("hotels") or []) if isinstance(x, dict)])
    seen = set()
    clean = []
    for item in candidates:
        name = str(item.get("name") or "").strip()
        if not name or _norm_place_name(name) in seen:
            continue
        seen.add(_norm_place_name(name))
        clean.append(item)
    clean = city_guard_for_candidates(clean, city, "route_candidates")
    if not clean:
        return _strict_insufficient_route(city, payload.get("budget") or {})
    if len(clean) < 2:
        card = _strict_insufficient_route(city, payload.get("budget") or {})
        card["summary"] = f"目前只找到 {len(clean)} 个{city}真实候选点，无法生成可信路线。"
        card["warnings"] = [f"{city}真实景点或餐饮候选不足", "已阻止使用其他城市或编造地点"]
        return card
    budget = payload.get("budget") if isinstance(payload.get("budget"), dict) else {}
    food_route = _user_wants_food_route(user_message)
    dining = [c for c in clean if _is_dining_candidate(c)]
    nondining = [c for c in clean if not _is_dining_candidate(c)]
    if not food_route and len(nondining) < 1:
        return _food_heavy_insufficient_route(city, budget)

    def _node(item, idx, arrival):
        is_din = _is_dining_candidate(item)
        price_num = _optional_int(str(item.get("price") or "").replace("¥", "").replace("元", ""), 0) or 0
        return {
            "day": 1, "step": idx, "name": item.get("name"),
            "type": item.get("type") or ("餐饮" if is_din else "景点"),
            "arrival_time": arrival,
            "stay_minutes": 75 if is_din else 90,
            "short_desc": item.get("reason") or ("用餐推荐，需二次确认营业状态" if is_din else "真实候选点位，建议结合地图确认"),
            "known_info": {"address": item.get("address") or "未知", "rating": item.get("rating") or "未知",
                            "price": item.get("price") or "未知", "opening_hours": item.get("opening_hours") or "未知"},
            "next_transport": "建议结合地图确认交通时间", "next_duration_minutes": 0,
            "estimated_cost": price_num, "data_source": item.get("data_source") or item.get("source_type") or "map_route",
            "display_source": item.get("display_source") or ("餐厅数据" if is_din else "地图数据"),
            "lat": item.get("lat"), "lng": item.get("lng"),
            "is_real_poi": bool(item.get("is_real_poi", True)),
            "can_order": is_din and item.get("data_source") != "needs_confirmation",
            "need_verify": True, "risk": "营业时间/排队需二次确认",
        }

    ordered = []
    if food_route:
        slots = ["09:30", "11:30", "14:00", "17:00", "19:00"]
        for i, item in enumerate(clean[:5]):
            ordered.append(_node(item, i + 1, slots[min(i, len(slots) - 1)]))
    else:
        nd, din = nondining[:4], dining[:2]
        seq = []
        if nd: seq.append((nd[0], "09:30"))
        if din: seq.append((din[0], "12:00"))
        if len(nd) > 1: seq.append((nd[1], "14:30"))
        if len(nd) > 2: seq.append((nd[2], "16:30"))
        if len(din) > 1: seq.append((din[1], "18:30"))
        elif len(nd) > 3: seq.append((nd[3], "17:30"))
        for i, (item, arr) in enumerate(seq[:6]):
            ordered.append(_node(item, i + 1, arr))

    print(f"[ROUTE_FROM_CANDIDATES] city={city} count={len(ordered)} names={[x.get('name') for x in ordered]}")
    ok, reason = validate_candidate_route_quality(ordered, food_route)
    if not ok:
        return _food_heavy_insufficient_route(city, budget) if ("餐饮" in reason) else _strict_insufficient_route(city, budget)

    title = f"{city}美食探店路线" if food_route else f"{city}景点与餐饮路线"
    summary = ("这是美食探店路线，不是完整景点游路线；点位需二次确认营业状态。" if food_route
               else "已根据景点与餐饮建议生成路线卡；点位来自地图参考/候选，需二次确认营业状态。")
    return {
        "answer_type": "trip_plan", "destination": city, "city": city,
        "data_status": "partial", "generated_from": "candidate_cards",
        "title": title, "route_title": title, "summary": summary,
        "route_map": ordered,
        "metrics": {"total_budget": budget.get("total"), "budget_per_person": budget.get("total"),
                     "route_intensity": "中低", "queue_risk": "需二次确认", "data_confidence": "真实候选点位，需二次确认营业状态"},
        "budget": budget,
        "warnings": (["美食探店路线，景点较少"] if food_route else ["部分点位需二次确认营业状态"]),
        "next_actions": ["查看地图路线", "换一家餐厅", "复制完整方案"],
        "tips": ["所有地点均来自真实候选数据。"],
        "actions": [],
    }

def _norm_place_name(value: str) -> str:
    return re.sub(r"\s+", "", unicodedata.normalize("NFKC", str(value or "")).lower())

def _route_json_prompt_context(user_message: str, tool_context: dict) -> dict:
    ctx = tool_context or {}
    req = ctx.get("requirements") if isinstance(ctx.get("requirements"), dict) else {}
    budget = ctx.get("budget") if isinstance(ctx.get("budget"), dict) else {}
    persona = ctx.get("persona") if isinstance(ctx.get("persona"), dict) else {}
    payload = _route_tool_payload(user_message, tool_context)
    return {
        **payload,
        "current_date": ctx.get("current_date") or _dt.now().date().isoformat(),
        "days": req.get("days"),
        "people": req.get("people_count") or req.get("people") or "",
        "need_hotel": bool(req.get("wants_hotel")),
        "need_meituan_real_resources": bool(req.get("wants_meituan") or req.get("requires_real_meituan")),
        "explicit_constraints": {
            "origin": req.get("origin") or "",
            "origin_is_default": bool(req.get("origin_is_default")),
            "avoid_meituan": bool((req.get("user_preference") or {}).get("avoid_meituan")),
        },
        "data_quality": ctx.get("data_quality") or {},
        "queue_monitor": ctx.get("queue_monitor") or {},
    }

def call_deepseek_route_json(user_message: str, tool_context: dict,
                             timeout_seconds: float = None,
                             max_attempts: int = 2) -> dict:
    """让 DeepSeek 基于轻量上下文生成正式路线地图卡；前端只消费通过校验的 route_map。"""
    if not _has_any_llm() or not isinstance(tool_context, dict):
        print("[DEEPSEEK_ROUTE_JSON_CALLED] skipped")
        print("[deepseek_route_json_raw]")
        print("[route_map_length]0")
        print("[route_map_names][]")
        print("[is_template_detected]False")
        return {}
    prompt_context = _route_json_prompt_context(user_message, tool_context)
    parsed_info = prompt_context.get("parsed_info") or {}
    allowed_names = prompt_context.get("allowed_place_names") or []
    context_brief = {
        "city": parsed_info.get("destination"),
        "budget_total": (prompt_context.get("budget") or {}).get("total"),
        "candidate_count": len(allowed_names),
        "data_tier": (prompt_context.get("data_quality") or {}).get("tier") if isinstance(prompt_context.get("data_quality"), dict) else None,
    }
    print(f"[DEEPSEEK_ROUTE_JSON_CALLED] city={context_brief.get('city')} attempt_max={max_attempts}")
    print(f"[TOOL_CONTEXT]{json.dumps(context_brief, ensure_ascii=False)}")
    # 真实性优先：没有真实候选地点时，绝不调用 LLM 编造路线。
    if len(allowed_names) < 2:
        print("[DEEPSEEK_ROUTE_JSON_CALLED] data_status=insufficient (not enough real POI, skip LLM)")
        _record_tool_call("deepseek_route_json", "skipped", 0, city=parsed_info.get("destination"), route_map_length=0)
        return _strict_insufficient_route(parsed_info.get("destination") or "", prompt_context.get("budget") or {})
    _ck = _route_json_cache_key(user_message, tool_context)
    _hit = _ROUTE_JSON_CACHE.get(_ck)
    if _hit and (time.time() - _hit[0]) < _ROUTE_JSON_TTL:
        cached = json.loads(json.dumps(_hit[1]))
        if validate_route_json(cached, allowed_names=allowed_names) and not detect_template_terms(cached):
            print("[ROUTE_JSON_CACHE_HIT]")
            _record_tool_call("deepseek_route_json", "success", 0, city=tool_context.get("city"), cached=True)
            return cached  # 深拷贝，避免下游修改污染缓存
        _ROUTE_JSON_CACHE.pop(_ck, None)
    last_raw = ""
    rewrite_note = ""
    for attempt in range(max(1, int(max_attempts or 1))):
        try:
            messages = [
                {
                    "role": "system",
                    "content": (
                        "你是一个真实本地生活与旅行规划 Agent。只输出合法 JSON，不输出 Markdown，不解释思考过程。\n"
                        "最高原则：所有推荐地点必须来自 user payload 的 tool_result；禁止编造 tool_result 中不存在的地点；禁止使用示例城市、默认城市、常见旅游模板。\n"
                        "用户明确目的地优先于当前位置；如果 tool_result 中地点不属于 parsed_info.destination，必须丢弃。\n"
                        "路线地图卡只能从 candidate_pool / allowed_place_names 中选点，place_name 必须与 allowed_place_names 精确一致；你的任务是排序和短说明，不是补点。\n"
                        "如果候选少于 2 个，或候选地点城市与 parsed_info.destination 不一致，输出 data_status=\"insufficient\"，route_items=[]。\n"
                        "禁止跨城市和模板点：新疆国际大巴扎、大理古城、黑油山景区、合肥、上海、北京、杭州、城市中心、老城慢走、午餐备选区、晚餐备选区、本地街巷散步、夜景慢逛。\n"
                        "如果 tool_result 为空或真实候选不足，输出 data_status=\"insufficient\"，route_items=[]，不得强行生成路线。\n"
                        "首屏最多输出 4 个 route_items；summary 不超过 40 个汉字；reason 不超过 20 个汉字；transport_note 不超过 24 个汉字；warnings 和 next_actions 最多 3 条。\n"
                        "不要在用户可见文案里写高德、美团、米其林、黑珍珠、RAG；display_source 只能写：地图数据、餐厅数据、酒店数据、本地生活数据。\n"
                        "输出格式：{\"answer_type\":\"trip_plan\",\"destination\":\"\",\"city\":\"\",\"data_status\":\"sufficient/partial/insufficient\",\"route_title\":\"\",\"summary\":\"\",\"route_items\":[{\"time\":\"上午\",\"place_name\":\"\",\"place_type\":\"attraction/restaurant/hotel/group_buy/local_life/transport\",\"source_type\":\"map_route/restaurant/hotel/group_buy/local_life\",\"display_source\":\"地图数据/餐厅数据/酒店数据/本地生活数据\",\"reason\":\"\",\"known_info\":{\"address\":\"未知\",\"rating\":\"未知\",\"price\":\"未知\",\"opening_hours\":\"未知\"},\"transport_note\":\"\"}],\"warnings\":[],\"next_actions\":[]}。\n"
                        "最终校验：route_items 中每个 place_name 必须精确来自 allowed_place_names；否则删除该项。"
                    ),
                },
                {
                    "role": "user",
                    "content": (
                        f"{rewrite_note}"
                        "User Payload：\n"
                        f"{json.dumps(prompt_context, ensure_ascii=False, indent=2)[:5200]}\n\n"
                        "任务：只基于 tool_result 生成非模板化路线。如果某类数据为空，不得编造。只输出 JSON。"
                    ),
                },
            ]
            t0 = time.perf_counter()
            resp = _llm_chat_completion({
                "messages": messages,
                "max_tokens": 500,
                "temperature": 0.2,
                "response_format": {"type": "json_object"},
                "_stream_collect": True,
            }, purpose="route_json", timeout_seconds=timeout_seconds)
            data = resp.json()
            text = _clean_markdown(data.get("choices", [{}])[0].get("message", {}).get("content", ""))
            last_raw = text or ""
            print(f"[deepseek_route_json_raw]{last_raw[:600]}")
            candidate = _parse_trip_plan_json(last_raw)
            names = [str(s.get("name") or "") for s in (candidate.get("route_map") or [])] if candidate else []
            print(f"[route_map_length]{len(names)}")
            print(f"[route_map_names]{names}")
            if candidate and candidate.get("data_status") != "insufficient":
                candidate = _normalize_trip_plan_json(candidate, {
                    "city": tool_context.get("city") or "",
                    "budget": tool_context.get("budget") if isinstance(tool_context.get("budget"), dict) else {},
                    "title": f"{tool_context.get('city','')}行程规划" if tool_context.get("city") else "",
                    "summary": "DeepSeek 已基于工具结果生成路线地图卡",
                })
            template_hits = detect_template_terms(candidate) if candidate else []
            print(f"[is_template_detected]{bool(template_hits)}")
            if template_hits:
                print(f"[template_terms]{template_hits[:8]}")
                rewrite_note = (
                    "上一版命中了模板词，必须重写一次。禁止使用以下表达："
                    f"{'、'.join(template_hits[:8])}\n"
                )
                if attempt < max(1, int(max_attempts or 1)) - 1:
                    print(f"[route_map_retry]attempt={attempt} reason=template_terms")
                    continue
                return {}
            if candidate and validate_route_json(candidate, allowed_names=allowed_names) and _route_city_guard_pass(candidate, parsed_info.get("destination") or tool_context.get("city") or "", allowed_names):
                route_names = [str(s.get("name") or "") for s in candidate.get("route_map", [])]
                print(f"[ROUTE_MAP_FROM_DEEPSEEK]{json.dumps({'title': candidate.get('title'), 'city': candidate.get('city'), 'route_map_length': len(route_names), 'route_map_names': route_names}, ensure_ascii=False)[:1200]}")
                _record_tool_call("deepseek_route_json", "success", round((time.perf_counter() - t0) * 1000), city=tool_context.get("city"), route_map_length=len(route_names))
                _ROUTE_JSON_CACHE[_ck] = (time.time(), json.loads(json.dumps(candidate)))
                return candidate
        except Exception as e:
            _record_tool_call("llm", "timeout" if "timeout" in str(e).lower() else "error", 0, purpose="route_json")
            print(f"[deepseek_route_json_error]{_safe_error_text(e)}")
        print(f"[route_map_retry]attempt={attempt} ok=False")
    if not last_raw:
        print("[deepseek_route_json_raw]")
        print("[route_map_length]0")
        print("[route_map_names][]")
        print("[is_template_detected]False")
    _record_tool_call("deepseek_route_json", "error", 0, city=tool_context.get("city"), route_map_length=0)
    return {}

def _deepseek_trip_final_text(planning_context: dict) -> str:
    card = call_deepseek_route_json(str((planning_context or {}).get("user_request", "")), planning_context or {})
    return json.dumps(card, ensure_ascii=False) if card else ""

def _parse_trip_plan_json(text: str) -> dict:
    raw = _clean_markdown(text or "")
    if not raw:
        return {}
    start, end = raw.find("{"), raw.rfind("}")
    if start >= 0 and end > start:
        raw = raw[start:end + 1]
    try:
        obj = json.loads(raw)
    except Exception:
        return {}
    if obj.get("answer_type") not in ("trip_plan", "map_first_trip_plan", None, ""):
        return {}
    if isinstance(obj.get("route_items"), list) and not isinstance(obj.get("route_map"), list):
        route_map = []
        for idx, item in enumerate(obj.get("route_items") or [], 1):
            if not isinstance(item, dict):
                continue
            known = item.get("known_info") if isinstance(item.get("known_info"), dict) else {}
            route_map.append({
                "day": 1,
                "step": idx,
                "name": item.get("place_name") or item.get("name") or "",
                "type": item.get("place_type") or item.get("type") or "",
                "arrival_time": {"上午": "09:30", "中午": "12:00", "下午": "15:00", "晚上": "18:30"}.get(str(item.get("time") or ""), str(item.get("time") or "")),
                "stay_minutes": 60,
                "short_desc": item.get("reason") or "",
                "next_transport": item.get("transport_note") or "",
                "next_duration_minutes": 0,
                "estimated_cost": 0,
                "data_source": item.get("source_type") or "",
                "display_source": item.get("display_source") or "",
                "known_info": known,
                "is_real_poi": True,
                "need_verify": True,
                "can_order": item.get("source_type") in ("hotel", "restaurant", "group_buy", "local_life"),
                "risk": "需二次确认",
            })
        obj["route_map"] = route_map
    if obj.get("data_status") == "insufficient" and not obj.get("route_map"):
        obj["answer_type"] = "trip_plan"
        obj["route_map"] = []
        return obj
    if not isinstance(obj.get("route_map"), list) or not obj["route_map"]:
        return {}
    obj["answer_type"] = "trip_plan"
    return obj

# 只拦"虚构占位/区域兜底"这类结构性模板词；不再拦 私房菜/老字号/海鲜排档/特色餐厅/本地小吃 等
# ——因为现在只喂真实 amap POI，这些词会合法出现在真实店名/描述里，拦了会误杀真实路线。
_ROUTE_TEMPLATE_BANNED = re.compile(
    r"代表性景区区域|代表性景区|核心商圈餐饮区域|核心商圈|商圈餐饮区域|本地菜餐饮区|"
    r"本地菜餐饮推荐|区域建议开场|历史文化街区|夜游/?滨水区域|景区区域|热门景点区域|"
    r"城市中心|老城慢走|本地街巷散步|午餐备选区|晚餐备选区|夜景慢逛|备选区|附近餐饮|"
    r"景点·|餐饮·|示例店|某某|泛化模板|模板路线|XX店"
)

def detect_template_terms(plan: dict) -> list:
    """检查标题、摘要、路线名和描述中的模板化表达。"""
    if not isinstance(plan, dict):
        return []
    fields = [plan.get("title", ""), plan.get("summary", "")]
    for step in plan.get("route_map") or []:
        if isinstance(step, dict):
            fields.extend([step.get("name", ""), step.get("short_desc", ""), step.get("reason", "")])
    hits = []
    for value in fields:
        text = str(value or "")
        if not text:
            continue
        m = _ROUTE_TEMPLATE_BANNED.search(text)
        if m:
            hits.append(m.group(0))
    return list(dict.fromkeys(hits))

def validate_route_json(obj: dict, allowed_names: list = None) -> bool:
    """校验 DeepSeek 生成的 route_map：只允许 1-4 个真实候选节点，不强行凑数/编造。"""
    if not isinstance(obj, dict):
        return False
    if obj.get("data_status") == "insufficient":
        return not bool(obj.get("route_map"))
    route_map = obj.get("route_map")
    if not isinstance(route_map, list) or len(route_map) < 2 or len(route_map) > 4:
        return False
    if detect_template_terms(obj):
        return False
    allowed = {_norm_place_name(x) for x in (allowed_names or []) if str(x or "").strip()}
    required = ("name", "type", "stay_minutes", "next_transport", "next_duration_minutes", "estimated_cost", "data_source", "is_real_poi", "need_verify", "can_order", "risk")
    for item in route_map:
        if not isinstance(item, dict):
            return False
        name = str(item.get("name") or "").strip()
        if not name:
            return False
        if allowed and _norm_place_name(name) not in allowed:
            print(f"[ROUTE_PLACE_REJECT] name={name} not_in_tool_result")
            return False
        if not (item.get("arrival_time") or item.get("time")):
            return False
        item.setdefault("stay_minutes", 60)
        item.setdefault("next_transport", "")
        item.setdefault("next_duration_minutes", 0)
        item.setdefault("estimated_cost", 0)
        item.setdefault("data_source", "area_suggestion")
        item.setdefault("is_real_poi", False)
        item.setdefault("need_verify", not bool(item.get("is_real_poi")))
        item.setdefault("can_order", False)
        item.setdefault("risk", "需二次确认" if item.get("need_verify") else "热门时段注意排队")
        for key in required:
            if key not in item:
                return False
        if _ROUTE_TEMPLATE_BANNED.search(name):
            return False
    return True

def _route_city_guard_pass(card: dict, city: str, allowed_names: list = None) -> bool:
    city_key = _guard_city_name(city)
    if not isinstance(card, dict):
        print(f"[ROUTE_CITY_GUARD_FAIL] city={city_key} reason=not_dict")
        return False
    if card.get("data_status") == "insufficient" and not card.get("route_map"):
        print(f"[ROUTE_CITY_GUARD_PASS] city={city_key} reason=insufficient_no_route")
        return True
    route_map = card.get("route_map") or []
    if not isinstance(route_map, list) or not route_map:
        print(f"[ROUTE_CITY_GUARD_FAIL] city={city_key} reason=empty_route")
        return False
    aliases = _city_allowed_aliases(city_key)
    allowed = {_norm_place_name(x) for x in (allowed_names or []) if str(x or "").strip()}
    card_city = _city_alias(str(card.get("city") or card.get("destination") or ""))
    if city_key and card_city and card_city != city_key and not (city_key == "福鼎" and card_city == "宁德"):
        print(f"[ROUTE_CITY_GUARD_FAIL] city={city_key} reason=card_city:{card_city}")
        return False
    for step in route_map:
        if not isinstance(step, dict):
            print(f"[ROUTE_CITY_GUARD_FAIL] city={city_key} reason=bad_step")
            return False
        name = str(step.get("name") or step.get("place_name") or "").strip()
        if allowed and _norm_place_name(name) not in allowed:
            print(f"[ROUTE_CITY_GUARD_FAIL] city={city_key} reason=not_in_candidate name={name}")
            return False
        text = _city_guard_text(step)
        other = _CROSS_CITY_TERMS_RE.search(text)
        if other and not any(a and a in text for a in aliases):
            print(f"[ROUTE_CITY_GUARD_FAIL] city={city_key} reason=cross_city_term:{other.group(0)} name={name}")
            return False
    print(f"[ROUTE_CITY_GUARD_PASS] city={city_key} count={len(route_map)}")
    return True

def _normalize_trip_plan_json(card: dict, plan: dict) -> dict:
    city = plan.get("city") or plan.get("render_city") or card.get("city") or "目的地"
    budget = plan.get("budget") or {}
    card["city"] = city
    card.setdefault("title", plan.get("title") or f"{city}行程规划")
    card.setdefault("summary", plan.get("summary") or f"🍊 {city}路线已生成")
    card.setdefault("metrics", {})
    card["metrics"].setdefault("total_budget", budget.get("total"))
    card["metrics"].setdefault("budget_per_person", budget.get("total"))
    card["metrics"].setdefault("route_intensity", "中低")
    card["metrics"].setdefault("queue_risk", "热门点排队，中午错峰")
    card["metrics"].setdefault("data_confidence", "基于真实候选点生成")
    card.setdefault("budget", {
        "transport": budget.get("transport", 0),
        "food": budget.get("food", 0),
        "activity": budget.get("tickets", 0),
        "tickets": budget.get("tickets", 0),
        "hotel": budget.get("hotel", 0),
        "snacks": budget.get("snacks", budget.get("local", 0)),
        "local": budget.get("local", 0),
        "buffer": budget.get("buffer", 0),
        "strategy": budget.get("strategy", _budget_strategy(budget.get("total", 0))),
        "status": budget.get("status", "未超支"),
    })
    if isinstance(card.get("budget"), dict):
        card["budget"].setdefault("total", budget.get("total", 0))
        card["budget"].setdefault("tickets", budget.get("tickets", card["budget"].get("activity", 0)))
        card["budget"].setdefault("snacks", budget.get("snacks", budget.get("local", 0)))
        card["budget"].setdefault("local", budget.get("local", 0))
        card["budget"].setdefault("strategy", budget.get("strategy", _budget_strategy(budget.get("total", 0))))
        card["budget"].setdefault("status", budget.get("status", "未超支"))
    for idx, step in enumerate(card.get("route_map") or [], 1):
        step["step"] = int(step.get("step") or idx)
        step["day"] = int(step.get("day") or 1)
        arrival = step.get("arrival_time") or step.get("time") or ("10:00" if idx == 1 else "")
        step["arrival_time"] = arrival
        step["time"] = arrival
        step.setdefault("stay_minutes", 60 if idx > 1 else 0)
        step.setdefault("short_desc", step.get("reason") or "基于工具结果与用户偏好排序")
        step.setdefault("next_transport", "")
        step.setdefault("next_duration_minutes", 0)
        step.setdefault("reason", "基于工具结果与用户偏好排序")
        step.setdefault("estimated_cost", 0)
        step.setdefault("data_source", "area_suggestion")
        step.setdefault("is_real_poi", False)
        step.setdefault("can_order", False)
        step.setdefault("need_verify", not bool(step.get("is_real_poi")))
        step.setdefault("risk", "需二次确认" if not step.get("is_real_poi") else "热门时段注意排队")
        if not step.get("is_real_poi"):
            step["can_order"] = False
            step["need_verify"] = True
    if not isinstance(card.get("tips"), list) or not card.get("tips"):
        card["tips"] = [
            f"{city}热门景点建议错峰前往，午餐 11:30 前或 13:30 后排队更短。",
            "出行前用地图工具确认营业时间与实时路况。",
            "标注“需二次确认”的候选点，下单前请核对营业和预订状态。",
        ]
    _spot_names = [s.get("name") for s in (card.get("route_map") or []) if s.get("name")]
    _first_spot = _spot_names[0] if _spot_names else city
    _route_pts = _spot_names[:5] if len(_spot_names) >= 2 else [city]
    # DeepSeek 可能生成 label 正确但 action_type 错误的按钮；这里统一清洗成前端可精准分发的动作（payload 填真实城市/节点）。
    card["actions"] = [
        {"label": "查看地图路线", "action_type": "open_amap_route", "requires_confirm": False,
         "payload": {"city": city, "route_points": _route_pts}},
        {"label": f"搜索{city}平价酒店", "action_type": "search_meituan_hotel", "requires_confirm": False,
         "payload": {"city": city, "keyword": "平价酒店", "price_high": 500}},
        {"label": f"🚕 打车去{_first_spot}", "action_type": "mock_taxi_order", "requires_confirm": False,
         "payload": {"from": "", "to": _first_spot if _spot_names else "", "city": city, "route_points": _route_pts}},
        {"label": "🚄 订高铁票", "action_type": "mock_train_order", "requires_confirm": True,
         "payload": {"from": city, "to": city, "date": ""}},
        {"label": "🏨 订酒店", "action_type": "mock_hotel_order", "requires_confirm": True,
         "payload": {"city": city, "keyword": "", "price_high": 500}},
    ]
    return card

def _coord_within_city(lat, lng, city: str, max_km: float = 80.0) -> bool:
    center = CITY_GEO_INDEX.get(_city_alias(city or "")) or {}
    clat, clng = _coerce_float(center.get("lat")), _coerce_float(center.get("lng"))
    lat, lng = _coerce_float(lat), _coerce_float(lng)
    if clat is None or clng is None or lat is None or lng is None:
        return True
    return _geo_distance_km({"lat": clat, "lng": clng}, {"lat": lat, "lng": lng}) <= max_km

def _attach_route_map_coords(card: dict, resources: list, city: str, allow_geocode: bool = True) -> dict:
    """把 DeepSeek route_map 节点回填高德/百度坐标，供前端绘制 Marker/Polyline。"""
    if not isinstance(card, dict):
        return card
    resources = resources or []
    need_geocode = []
    for step in card.get("route_map") or []:
        if _coerce_float(step.get("lat")) is not None and _coerce_float(step.get("lng")) is not None:
            continue
        name = str(step.get("name") or "").strip()
        matched = None
        for item in resources:
            iname = str((item or {}).get("name") or "").strip()
            if iname and (iname == name or iname in name or name in iname):
                matched = item
                break
        if matched:
            lat, lng = _coerce_float(matched.get("lat")), _coerce_float(matched.get("lng"))
            if lat is None or lng is None:
                loc = _extract_coord_pair(matched.get("location"))
                if loc:
                    lat, lng = loc.get("lat"), loc.get("lng")
            if lat is not None and lng is not None:
                if not _coord_within_city(lat, lng, city):
                    print(f"[ROUTE_COORD_REJECT] city={city} name={name} lat={lat} lng={lng} source=resource_match")
                    need_geocode.append(step)
                    continue
                step["lat"], step["lng"] = lat, lng
                step["coord_source"] = matched.get("data_source") or matched.get("source") or "resource_match"
                continue
        if name:
            need_geocode.append(step)
    if need_geocode and not allow_geocode:
        center = CITY_GEO_INDEX.get(_city_alias(city)) or {}
        base_lat, base_lng = _coerce_float(center.get("lat")), _coerce_float(center.get("lng"))
        if base_lat is not None and base_lng is not None:
            for idx, step in enumerate(need_geocode):
                step["lat"] = round(base_lat + (idx - 2) * 0.006, 6)
                step["lng"] = round(base_lng + (idx - 2) * 0.006, 6)
                step["coord_source"] = "city_center_offset"
        return card
    # ✅ 并行地理编码剩余节点：原来按节点串行(N×6s)，并行后≈1×6s，大幅缩短整体规划耗时
    if need_geocode:
        def _geo_step(step):
            nm = str(step.get("name") or "").strip()
            return step, (geocode_amap(f"{city}{nm}", city) or geocode_baidu(f"{city}{nm}", city))
        with ThreadPoolExecutor(max_workers=min(6, len(need_geocode))) as pool:
            for step, loc in pool.map(_geo_step, need_geocode):
                if loc:
                    lat, lng = loc.get("lat"), loc.get("lng")
                    if not _coord_within_city(lat, lng, city):
                        print(f"[ROUTE_COORD_REJECT] city={city} name={step.get('name')} lat={lat} lng={lng} source=geocode")
                        continue
                    step["lat"], step["lng"] = lat, lng
                    step["coord_source"] = "amap_geocode" if loc.get("data_source") == "amap" else "baidu_geocode"
    return card


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
    if isinstance(plan.get("route_card"), dict) and plan["route_card"].get("answer_type") == "trip_plan":
        return json.dumps(plan["route_card"], ensure_ascii=False)
    if not plan.get("success", True):
        return _clean_markdown(plan.get("error") or "真实地点数据不足，不生成模板路线。")
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
        intent_input = {
            "destination": req.get("destination"),
            "days": req.get("days"),
            "budget": req.get("budget"),
            "commerce_mode": req.get("commerce_mode"),
            "planner_mode": req.get("planner_mode"),
        }
        print(f"[INTENT_DETECTED] destination={req.get('destination')} intent={req.get('intent')} planner={req.get('planner_mode')}")
        yield f"data: {json.dumps({'type':'step_start','id':1,'tool':'deepseek_intent','input':intent_input}, ensure_ascii=False)}\n\n"
        intent_summary = f"已识别：{req.get('destination')} · {req.get('days')}天 · 预算{req.get('budget')}元"
        yield f"data: {json.dumps({'type':'step_done','id':1,'tool':'deepseek_intent','result':{'success':True, **intent_input},'summary':intent_summary}, ensure_ascii=False)}\n\n"
        longcat_input = {"city": req.get("destination"), "user_prompt": user_message, "resource_types": ["hotel", "restaurant", "sight", "groupbuy"], "limit": 8}
        # 普通出游规划不强调美团真实资源；仅在用户明确美团意图时才在任务树展示美团龙猫/美团 Skill 步骤
        can_show_meituan = _requires_meituan_real_resources(user_message) and not req.get("user_preference", {}).get("avoid_meituan")
        print(f"[MEITUAN_INTENT_REQUIRED] {str(bool(can_show_meituan)).lower()}")
        mt_intent = "hotel_search" if req.get("wants_hotel") else "restaurant_search"
        mt_keyword = "酒店" if req.get("wants_hotel") else "本地菜 团购"
        mt_category = _meituan_category_from_intent(mt_intent, mt_keyword)
        mt_pool = None
        mt_future = None
        mt_t0 = None
        mt_deferred = False
        mt_results = []
        if can_show_meituan:
            yield f"data: {json.dumps({'type':'step_start','id':2,'tool':'longcat_resource_search','input':longcat_input}, ensure_ascii=False)}\n\n"
            mt_input = {"intent": mt_intent, "city": req.get("destination"), "keyword": mt_keyword, "limit": 6}
            yield f"data: {json.dumps({'type':'step_start','id':4,'tool':'call_meituan_skill','input':mt_input}, ensure_ascii=False)}\n\n"
            # 美团真实资源放后台线程，与行程规划并行；主流程不阻塞等待
            mt_pool = ThreadPoolExecutor(max_workers=1)
            mt_t0 = time.time()
            print(f"[MEITUAN_REAL_QUERY_START] city={req.get('destination')} intent={mt_intent} keyword={mt_keyword}")
            mt_future = mt_pool.submit(tool_call_meituan_skill, mt_intent, req.get("destination"), mt_keyword, "", None, None, {}, 6)
        yield f"data: {json.dumps({'type':'step_start','id':3,'tool':tool_name,'input':args}, ensure_ascii=False)}\n\n"
        plan = tool_plan_meituan_trip(**args)
        lc_payload = plan.get("longcat_resources") if isinstance(plan.get("longcat_resources"), dict) else {"success": False, "message": "美团龙猫暂不可用，已切换备用数据源"}
        if can_show_meituan:
            yield f"data: {json.dumps({'type':'step_done','id':2,'tool':'longcat_resource_search','result':lc_payload,'summary':_tool_summary('longcat_resource_search', longcat_input, lc_payload)}, ensure_ascii=False)}\n\n"
            # 主流程最多前台等 3s（规划本身已耗时，通常此处直接转后台补充）
            try:
                mt_res = mt_future.result(timeout=max(0.1, mt_t0 + MEITUAN_FOREGROUND_TIMEOUT - time.time()))
                mt_results = _enrich_real_merchant_fields([x for x in (mt_res.get("results") or []) if _is_real_meituan_item(x)])
            except FuturesTimeout:
                mt_deferred = True
                print("[MEITUAN_REAL_QUERY_TIMEOUT] foreground")
            except Exception:
                mt_deferred = True
            if mt_results:
                print(f"[MEITUAN_REAL_RESULTS_COUNT] {len(mt_results)}")
                mt_payload = {"success": True, "city": req.get("destination"), "keyword": mt_keyword,
                              "count": len(mt_results), "results": mt_results[:6], "source": "meituan_skill", "is_real_meituan": True}
            else:
                mt_deferred = True
                if not mt_results:
                    print("[MEITUAN_REAL_QUERY_TIMEOUT] foreground_no_result")
                mt_payload = {"success": False, "pending": True, "city": req.get("destination"), "keyword": mt_keyword,
                              "source": "meituan_skill", "message": "美团真实资源正在后台补充，当前先生成可执行方案"}
            yield f"data: {json.dumps({'type':'step_done','id':4,'tool':'call_meituan_skill','result':mt_payload,'summary':_tool_summary('call_meituan_skill', mt_input, mt_payload)}, ensure_ascii=False)}\n\n"
        if plan.get("success") and plan.get("queue_monitor"):
            monitor_payload = {"success": True, "monitor": plan.get("queue_monitor")}
            monitor_input = {"resource_type": "queue", "target_name": plan.get("queue_monitor", {}).get("target_name"), "city": plan.get("city")}
            yield f"data: {json.dumps({'type':'step_start','id':5,'tool':'mock_start_service_monitor','input':monitor_input}, ensure_ascii=False)}\n\n"
            yield f"data: {json.dumps({'type':'step_done','id':5,'tool':'mock_start_service_monitor','result':monitor_payload,'summary':_tool_summary('mock_start_service_monitor', monitor_input, monitor_payload)}, ensure_ascii=False)}\n\n"
        if plan.get("success") and plan.get("pending_order"):
            order_payload = {"success": True, "order": plan["pending_order"]}
            order_input = {
                "order_type": plan["pending_order"].get("order_type", "trip_bundle"),
                "item": plan["pending_order"].get("item", {}),
            }
            yield f"data: {json.dumps({'type':'step_start','id':6,'tool':'create_pending_order','input':order_input}, ensure_ascii=False)}\n\n"
            yield f"data: {json.dumps({'type':'step_done','id':6,'tool':'create_pending_order','result':order_payload,'summary':_tool_summary('create_pending_order', {}, order_payload)}, ensure_ascii=False)}\n\n"
        final_text = ""
        if plan.get("success") and plan.get("route_card"):
            final_text = json.dumps(plan["route_card"], ensure_ascii=False)
        sm = _tool_summary(tool_name, args, plan)
        yield f"data: {json.dumps({'type':'step_done','id':3,'tool':tool_name,'result':plan,'summary':sm}, ensure_ascii=False)}\n\n"
        yield f"data: {json.dumps({'type':'final','text':final_text or _meituan_trip_final_text(plan)}, ensure_ascii=False)}\n\n"
        if can_show_meituan and mt_results and not mt_deferred:
            yield f"data: {json.dumps(_meituan_append_payload(True, req.get('destination'), mt_category, mt_results, '已补充美团真实资源，可替换进路线 / 生成 Mock 取号或预订', mt_keyword), ensure_ascii=False)}\n\n"
        # 后台补充：美团真实商户在 MEITUAN_BACKGROUND_TIMEOUT 内返回则追加商户卡，否则提示已用备用方案
        if can_show_meituan and mt_deferred and mt_future is not None:
            try:
                bg = mt_future.result(timeout=max(1.0, mt_t0 + MEITUAN_BACKGROUND_TIMEOUT - time.time()))
            except Exception:
                bg = {}
            bg_real = _enrich_real_merchant_fields([x for x in (bg.get("results") or []) if _is_real_meituan_item(x)]) if isinstance(bg, dict) else []
            if bg_real:
                append_payload = _meituan_append_payload(
                    True, req.get("destination"), mt_category, bg_real,
                    "已补充美团真实资源，可替换进路线 / 生成 Mock 取号或预订", mt_keyword
                )
            else:
                append_payload = _meituan_append_payload(
                    False, req.get("destination"), mt_category, [],
                    "美团真实资源暂未返回，当前可使用 Mock 演示", mt_keyword
                )
            yield f"data: {json.dumps(append_payload, ensure_ascii=False)}\n\n"
        if mt_pool is not None:
            mt_pool.shutdown(wait=False)
    return Response(stream_with_context(generate()), mimetype="text/event-stream",
                    headers={"Cache-Control":"no-cache","X-Accel-Buffering":"no"})

def _rule_public_facility_agent_response(user_message: str, city_hint: str) -> Response:
    def generate():
        args = _direct_public_facility_input(user_message, city_hint)
        print(f"[RULE_ROUTER] public_facility_search city={args.get('city')} keyword={args.get('keyword')}")
        yield f"data: {json.dumps({'type':'step_start','id':1,'tool':'public_facility_search','input':args}, ensure_ascii=False)}\n\n"
        t0 = time.perf_counter()
        items = []
        used_radius = int(args.get("radius") or 0)
        radius_attempts = []
        coords_ok = args.get("user_lat") is not None and args.get("user_lng") is not None
        public_radii = [int(args["explicit_radius"])] if args.get("explicit_radius") else [500, 1000, 2000]
        support_radii = [int(args["explicit_radius"])] if args.get("explicit_radius") else [500, 1000, 2000, 3000]
        final_radii = [int(args["explicit_radius"])] if args.get("explicit_radius") else [5000, 8000, 12000]
        stage_defs = [
            {
                "stage": "explicit_toilet",
                "label": "明确厕所",
                "osm": "public_toilet",
                "radii": public_radii,
                "keywords": ["toilet", "restroom", "public toilet", "washroom", "bathroom", "卫生间", "公厕", "洗手间", "厕所"],
                "nominatim": ["toilet", "restroom"],
                "amap_types": "200300",  # 高德公共厕所类型码（部分地区有真实厕所POI）
            },
            {
                "stage": "mall",
                "label": "商场厕所",
                "osm": "mall",
                "radii": support_radii,
                "keywords": ["shopping mall", "mall", "商场", "购物中心"],
                "nominatim": ["shopping mall"],
                "amap_types": "060000",  # 购物服务（含商场/购物中心）
            },
            {
                "stage": "station",
                "label": "地铁站厕所",
                "osm": "station",
                "radii": support_radii,
                "keywords": ["MRT station", "metro station", "subway station", "地铁站", "车站"],
                "nominatim": ["MRT station", "metro station", "subway station"],
                "amap_types": "150500|150200",  # 地铁站|火车站
            },
            {
                "stage": "likely",
                "label": "可能有卫生间的地点",
                "osm": "likely",
                "radii": support_radii,
                "keywords": [
                    "park", "petrol station", "gas station", "library", "community center",
                    "hawker centre", "food court", "cafe", "convenience store", "tourist information center",
                    "公园", "加油站", "图书馆", "社区中心", "餐饮中心", "咖啡店", "便利店", "游客中心", "学校", "高校",
                ],
                "nominatim": ["park", "petrol station", "library", "food court", "cafe", "convenience store"],
                "amap_types": "110100|010100|050300|050500",  # 公园广场|加油站|快餐厅|咖啡厅
            },
            {
                "stage": "core_backup",
                "label": "核心备用地点",
                "osm": "core_backup",
                "radii": final_radii,
                "keywords": ["shopping mall", "MRT station", "park", "petrol station", "商场", "地铁站", "公园", "加油站"],
                "nominatim": ["shopping mall", "MRT station", "park", "petrol station"],
                "amap_types": "060000|150500|110100|010100",  # 商场|地铁站|公园|加油站
            },
        ]
        if args.get("keyword") != "公共厕所":
            preferred = "mall" if args["keyword"] == "商场" else "station" if args["keyword"] == "地铁站" else "likely"
            stage_defs = [s for s in stage_defs if s["stage"] == preferred] + [s for s in stage_defs if s["stage"] != preferred]

        def _keyword_label(keyword: str) -> str:
            if re.search(r"toilet|restroom|washroom|bathroom|卫生间|公厕|洗手间|厕所", keyword, flags=re.I):
                return "公共卫生间"
            if re.search(r"mall|商场|购物中心", keyword, flags=re.I):
                return "商场"
            if re.search(r"MRT|metro|subway|station|地铁|车站", keyword, flags=re.I):
                return "地铁站"
            if re.search(r"petrol|gas|fuel|加油", keyword, flags=re.I):
                return "加油站"
            if re.search(r"park|公园", keyword, flags=re.I):
                return "公园"
            if re.search(r"cafe|coffee|咖啡", keyword, flags=re.I):
                return "咖啡店"
            if re.search(r"convenience|便利", keyword, flags=re.I):
                return "便利店"
            if re.search(r"library|图书馆", keyword, flags=re.I):
                return "图书馆"
            if re.search(r"community|社区", keyword, flags=re.I):
                return "社区中心"
            if re.search(r"tourist|游客", keyword, flags=re.I):
                return "游客中心"
            if re.search(r"school|university|高校|学校|大学", keyword, flags=re.I):
                return "高校"
            return keyword

        def _dedupe_nearby(rows):
            seen = set()
            out = []
            for row in rows or []:
                key = row.get("location") or row.get("name")
                if not key or key in seen:
                    continue
                seen.add(key)
                out.append(row)
            def _dist(row):
                try:
                    return int(float(row.get("distance") or 999999))
                except Exception:
                    return 999999
            return sorted(out, key=_dist)

        def _run_stage(stage: dict) -> tuple[list, int]:
            for radius in stage["radii"]:
                batch = []
                if coords_ok:
                    # 高德周边类型搜索：把商场/地铁站/加油站/公园/快餐当成派生厕所点(距离=场所距离)
                    if stage.get("amap_types"):
                        amap_rows = search_amap_around_facility(
                            float(args["user_lat"]),
                            float(args["user_lng"]),
                            stage["amap_types"],
                            radius,
                            args["limit"],
                        )
                        for row in amap_rows or []:
                            row["facility_stage"] = stage["stage"]
                            row["facility_query"] = row.get("facility_query") or stage["label"]
                        batch.extend(amap_rows or [])
                    if stage["osm"] == "public_toilet":
                        osm_rows = search_public_toilets_osm(float(args["user_lat"]), float(args["user_lng"]), radius, args["limit"])
                    else:
                        osm_rows = search_nearby_toilet_support_osm(
                            float(args["user_lat"]),
                            float(args["user_lng"]),
                            radius,
                            args["limit"],
                            stage["osm"],
                        )
                    for row in osm_rows or []:
                        row["facility_stage"] = stage["stage"]
                        row["facility_query"] = row.get("facility_query") or stage["label"]
                    batch.extend(osm_rows or [])
                    nom_rows = search_nearby_toilet_nominatim(
                        float(args["user_lat"]),
                        float(args["user_lng"]),
                        stage.get("nominatim") or stage["keywords"][:3],
                        radius,
                        args["limit"],
                        stage["stage"],
                    )
                    for row in nom_rows or []:
                        row["facility_stage"] = stage["stage"]
                        row["facility_query"] = row.get("facility_query") or stage["label"]
                    batch.extend(nom_rows or [])
                    deduped = _dedupe_nearby(batch)
                    if deduped:
                        radius_attempts.append({
                            "stage": stage["stage"],
                            "label": stage["label"],
                            "radius": radius,
                            "count": len(deduped or []),
                        })
                        return deduped[:args["limit"]], radius
                for keyword in stage["keywords"]:
                    part = search_amap_place(
                        keyword,
                        args["city"],
                        args["limit"],
                        location=args.get("location", ""),
                        radius=radius or 2000,
                    )
                    for row in part or []:
                        row["facility_stage"] = stage["stage"]
                        row["facility_query"] = _keyword_label(keyword)
                    batch.extend(part or [])
                deduped = _dedupe_nearby(batch)
                radius_attempts.append({
                    "stage": stage["stage"],
                    "label": stage["label"],
                    "radius": radius,
                    "count": len(deduped or []),
                })
                if deduped:
                    return deduped[:args["limit"]], radius
            return [], stage["radii"][-1] if stage["radii"] else 0

        if coords_ok:
            for stage in stage_defs:
                batch, stage_radius = _run_stage(stage)
                used_radius = stage_radius
                if batch:
                    items = batch
                    args["keyword"] = stage["label"]
                    break
            # 兜底保证：前面所有阶段都没结果时，用最大半径把高德全部支持类型 + OSM 一起扫一遍，
            # 取最近的可借厕所地点，绝不返回"找不到、建议去商场/地铁"的空模板。
            if not items:
                lat_f, lng_f = float(args["user_lat"]), float(args["user_lng"])
                all_types = "|".join(AMAP_TOILET_SUPPORT_TYPES.keys())
                last_resort = []
                for radius in (3000, 5000, 8000, 12000):
                    last_resort = search_amap_around_facility(lat_f, lng_f, all_types, radius, args["limit"])
                    if not last_resort:
                        last_resort = search_nearby_toilet_support_osm(lat_f, lng_f, radius, args["limit"], "all")
                    if not last_resort:
                        last_resort = search_nearby_toilet_nominatim(
                            lat_f, lng_f,
                            ["shopping mall", "MRT station", "park", "petrol station", "convenience store"],
                            radius, args["limit"], "core_backup",
                        )
                    if last_resort:
                        used_radius = radius
                        break
                if last_resort:
                    for row in last_resort:
                        row["facility_stage"] = "last_resort"
                        row["facility_query"] = row.get("facility_query") or row.get("type") or "可尝试地点"
                    items = _dedupe_nearby(last_resort)[:args["limit"]]
                    args["keyword"] = "附近可借卫生间的地点"
                    radius_attempts.append({"stage": "last_resort", "label": "兜底最近地点",
                                            "radius": used_radius, "count": len(items)})
        else:
            args["keyword"] = "厕所定位"

        if items:
            first_query = items[0].get("facility_query")
            if first_query and args["keyword"] == "公共厕所":
                args["keyword"] = first_query
        elapsed = round((time.perf_counter() - t0) * 1000)
        map_url = _amap_map_link(
            f"https://ditu.amap.com/search?query={quote(args['keyword'])}"
            + (f"&query_type=RQBXY&longitude={args['location'].split(',')[0]}&latitude={args['location'].split(',')[1]}&range={used_radius or 2000}" if args.get("location") and "," in args["location"] else ""),
            city=args["city"],
            keyword=args["keyword"],
        )
        reply_payload = _nearby_toilet_reply_payload(args, items)
        result = {
            "success": bool(reply_payload.get("results")),
            "reply_type": "nearby_toilet_results",
            "intent": "nearby_toilet_finder",
            "data_source": "map",
            "tool_name": "nearby-toilet-finder",
            "elapsed_ms": int(elapsed),
            "city": args["city"],
            "keyword": args["keyword"],
            "radius": used_radius,
            "radius_attempts": radius_attempts,
            "count": len(reply_payload.get("results") or []),
            "results": reply_payload.get("results") or [],
            "reply_payload": reply_payload,
            "source": "map",
            "map_url": map_url,
            "message": ("" if reply_payload.get("results")
                        else ("附近暂时没搜到可借卫生间的地点，可点击扩大范围或稍后重试。" if coords_ok
                              else "请开启定位或发送经纬度后再查找。")),
        }
        yield f"data: {json.dumps({'type':'step_done','id':1,'tool':'public_facility_search','result':result,'summary':_tool_summary('public_facility_search', args, result)}, ensure_ascii=False)}\n\n"
        link_payload = {
            "success": bool(map_url),
            "data_source": "amap",
            "tool_name": "amap-lbs-skill",
            "elapsed_ms": 0,
            "city": args["city"],
            "map_url": map_url,
            "keyword": args["keyword"],
        }
        yield f"data: {json.dumps({'type':'step_start','id':2,'tool':'amap_map_link','input':{'city':args['city'],'keyword':args['keyword']}}, ensure_ascii=False)}\n\n"
        yield f"data: {json.dumps({'type':'step_done','id':2,'tool':'amap_map_link','result':link_payload,'summary':_tool_summary('amap_map_link', {}, link_payload)}, ensure_ascii=False)}\n\n"
        text = _public_facility_fallback_text(user_message, result)
        task_state = {}
        if not reply_payload.get("results"):
            coord_suffix = ""
            if args.get("user_lat") is not None and args.get("user_lng") is not None:
                coord_suffix = f"（我的当前位置：纬度{float(args['user_lat']):.5f},经度{float(args['user_lng']):.5f}）"
            task_state["options"] = [
                {"option_type": "quick_action", "label": "查附近商场", "message": f"查附近商场厕所{coord_suffix}"},
                {"option_type": "quick_action", "label": "查附近地铁站", "message": f"查附近地铁站厕所{coord_suffix}"},
                {"option_type": "quick_action", "label": "查附近公园", "message": f"查附近公园厕所{coord_suffix}"},
                {"option_type": "quick_action", "label": "扩大范围", "message": f"找厕所 扩大到3公里{coord_suffix}"},
            ]
        yield f"data: {json.dumps({'type':'final','text':text,'payload':reply_payload,'task_state':task_state}, ensure_ascii=False)}\n\n"
    return Response(stream_with_context(generate()), mimetype="text/event-stream",
                    headers={"Cache-Control":"no-cache","X-Accel-Buffering":"no"})

def _rule_meituan_resource_agent_response(user_message: str, city_hint: str) -> Response:
    def generate():
        args = _direct_meituan_skill_input(user_message, city_hint)
        category = _meituan_category_from_intent(args.get("intent", ""), args.get("keyword", ""))
        print(f"[INTENT_DETECTED] direct_meituan_resource city={args.get('city')} intent={args.get('intent')} keyword={args.get('keyword')}")
        print("[MEITUAN_INTENT_REQUIRED] true")
        lc_input = {"city": args["city"], "user_prompt": user_message, "resource_types": [args.get("intent", "restaurant_search")], "limit": args["limit"]}
        yield f"data: {json.dumps({'type':'step_start','id':1,'tool':'longcat_resource_search','input':lc_input}, ensure_ascii=False)}\n\n"
        lc_result = tool_call_longcat_resource_search(args["city"], user_message, [args.get("intent", "restaurant_search")], args["limit"])
        yield f"data: {json.dumps({'type':'step_done','id':1,'tool':'longcat_resource_search','result':lc_result,'summary':_tool_summary('longcat_resource_search', lc_input, lc_result)}, ensure_ascii=False)}\n\n"

        # 美团真实资源较慢(mttravel 实测约18s)：放到后台线程，主流程最多等 MEITUAN_FOREGROUND_TIMEOUT(3s)。
        # 3s 内返回则直接展示真实资源；超时则先用高德/Mock 出可执行方案，美团结果由后台补充并追加卡片。
        yield f"data: {json.dumps({'type':'step_start','id':2,'tool':'call_meituan_skill','input':args}, ensure_ascii=False)}\n\n"
        mt_pool = ThreadPoolExecutor(max_workers=1)
        mt_t0 = time.perf_counter()
        print(f"[MEITUAN_REAL_QUERY_START] city={args['city']} intent={args['intent']} keyword={args['keyword']}")
        mt_future = mt_pool.submit(
            tool_call_meituan_skill,
            args["intent"], args["city"], args["keyword"], args["location"],
            args["user_lat"], args["user_lng"], args["filters"], args["limit"],
        )
        meituan_deferred = False
        try:
            result = mt_future.result(timeout=MEITUAN_FOREGROUND_TIMEOUT)
        except FuturesTimeout:
            meituan_deferred = True
            print("[MEITUAN_REAL_QUERY_TIMEOUT] foreground")
            result = {"success": False, "intent": args["intent"], "city": args["city"],
                      "keyword": args["keyword"], "source": "meituan_skill", "is_real_meituan": False}
        if meituan_deferred:
            pending_payload = {"success": False, "pending": True, "city": args["city"],
                               "keyword": args["keyword"], "source": "meituan_skill",
                               "message": "美团真实资源正在后台补充，当前先生成可执行方案"}
            yield f"data: {json.dumps({'type':'step_done','id':2,'tool':'call_meituan_skill','result':pending_payload,'summary':'美团真实资源后台补充中'}, ensure_ascii=False)}\n\n"
        else:
            print(f"[MEITUAN_REAL_RESULTS_COUNT] {len(result.get('results') or [])}")
            yield f"data: {json.dumps({'type':'step_done','id':2,'tool':'call_meituan_skill','result':result,'summary':_tool_summary('call_meituan_skill', args, result)}, ensure_ascii=False)}\n\n"

        amap_keyword = _amap_keyword_from_resource_args(args)
        amap_input = {"city": args["city"], "keyword": amap_keyword, "limit": args["limit"]}
        if args.get("user_lat") and args.get("user_lng"):
            amap_input.update({
                "location": f"{args['user_lng']},{args['user_lat']}",
                "radius": args.get("filters", {}).get("distance_radius", 5000),
            })
        yield f"data: {json.dumps({'type':'step_start','id':3,'tool':'amap_poi','input':amap_input}, ensure_ascii=False)}\n\n"
        amap_t0 = time.perf_counter()
        amap_items = search_amap_place(
            amap_keyword,
            args["city"],
            args["limit"],
            location=amap_input.get("location", ""),
            radius=amap_input.get("radius", 3000),
        )
        amap_elapsed = round((time.perf_counter() - amap_t0) * 1000)
        amap_result = _amap_poi_payload(args["city"], amap_keyword, amap_items, amap_elapsed)
        yield f"data: {json.dumps({'type':'step_done','id':3,'tool':'amap_poi','result':amap_result,'summary':_tool_summary('amap_poi', amap_input, amap_result)}, ensure_ascii=False)}\n\n"
        # ── 主流程方案：仅用 3s 内已拿到的数据（美团真实结果 / 高德 POI / Mock 兜底），不阻塞等待美团 ──
        fg_has_real = bool((not meituan_deferred) and result.get("results"))
        if fg_has_real:
            _enrich_real_merchant_fields(result.get("results"))
        has_real = bool(fg_has_real or amap_result.get("results"))
        mock_items = []
        if not has_real:
            mock_items = _mock_resource_fallback(args["city"], amap_keyword, args.get("intent", ""))
            print("[MOCK_FALLBACK_USED] direct_meituan_resource")
            print("[MOCK_MARKED_AS_NON_REAL]")
            result = {**result, "success": True, "results": mock_items, "count": len(mock_items),
                      "source": "mock_fallback", "fallback": True}
        pending_order = {}
        if fg_has_real and result.get("results") and _looks_order_draft_request(user_message):
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
            yield f"data: {json.dumps({'type':'step_start','id':4,'tool':'create_pending_order','input':{'order_type':order_type,'item':item}}, ensure_ascii=False)}\n\n"
            yield f"data: {json.dumps({'type':'step_done','id':4,'tool':'create_pending_order','result':order_result,'summary':_tool_summary('create_pending_order', {}, order_result)}, ensure_ascii=False)}\n\n"
        if mock_items:
            lines = [f"暂未获取到{args['city']}美团真实商户资源，已切换备用数据源。以下为 Mock 演示数据，不代表真实商户："]
            for i, it in enumerate(mock_items[:5], 1):
                lines.append(f"{i}. {it['name']} · ¥{it.get('cost','-')} · 评分{it.get('rating','-')} · {it.get('address','')}")
            lines.append("以上为 Mock 演示数据，不可生成真实订单；可继续让我帮你打车、订酒店/门票或生成路线地图。")
            text = "\n".join(lines)
        else:
            text = _deepseek_resource_fusion_text(user_message, amap_result, result)
        if pending_order.get("order_id"):
            text += f"\n已生成待确认订单 {pending_order['order_id']}，请在卡片中确认后执行模拟下单。"
        if meituan_deferred:
            text += "\n🍊 美团真实资源正在后台补充，稍候将自动追加真实商户卡片。"
        yield f"data: {json.dumps({'type':'final','text':text}, ensure_ascii=False)}\n\n"
        if fg_has_real and result.get("results"):
            yield f"data: {json.dumps(_meituan_append_payload(True, args['city'], category, result.get('results') or [], '已补充美团真实资源，可替换进路线 / 生成 Mock 取号或预订', args['keyword']), ensure_ascii=False)}\n\n"

        # ── 后台补充：美团结果在 MEITUAN_BACKGROUND_TIMEOUT(20s)内返回则追加真实商户卡片；仍无则提示已用备用方案 ──
        if meituan_deferred:
            remaining = max(1, MEITUAN_BACKGROUND_TIMEOUT - (time.perf_counter() - mt_t0))
            try:
                bg = mt_future.result(timeout=remaining)
            except FuturesTimeout:
                bg = {"success": False}
            except Exception as e:
                bg = {"success": False, "error": _safe_error_text(e)}
            bg_real = bg.get("results") if (isinstance(bg, dict) and bg.get("success")) else []
            if bg_real:
                _enrich_real_merchant_fields(bg_real)
                append_payload = _meituan_append_payload(
                    True, args["city"], category, bg_real,
                    "已补充美团真实资源，可替换进路线 / 生成 Mock 取号或预订", args["keyword"]
                )
            else:
                append_payload = _meituan_append_payload(
                    False, args["city"], category, [],
                    "美团真实资源暂未返回，当前可使用 Mock 演示", args["keyword"]
                )
            yield f"data: {json.dumps(append_payload, ensure_ascii=False)}\n\n"
        mt_pool.shutdown(wait=False)
    return Response(stream_with_context(generate()), mimetype="text/event-stream",
                    headers={"Cache-Control":"no-cache","X-Accel-Buffering":"no"})

def _rule_amap_route_response(user_message: str, city_hint: str) -> Response:
    def generate():
        route_input = {"message": user_message, "city": city_hint}
        yield f"data: {json.dumps({'type':'step_start','id':1,'tool':'amap_route','input':route_input}, ensure_ascii=False)}\n\n"
        route_result, link_result = _amap_route_payload(user_message, city_hint)
        yield f"data: {json.dumps({'type':'step_done','id':1,'tool':'amap_route','result':route_result,'summary':_tool_summary('amap_route', route_input, route_result)}, ensure_ascii=False)}\n\n"
        yield f"data: {json.dumps({'type':'step_start','id':2,'tool':'amap_map_link','input':{'city':route_result.get('city'),'waypoints':route_result.get('waypoints', [])}}, ensure_ascii=False)}\n\n"
        yield f"data: {json.dumps({'type':'step_done','id':2,'tool':'amap_map_link','result':link_result,'summary':_tool_summary('amap_map_link', {}, link_result)}, ensure_ascii=False)}\n\n"
        if route_result.get("success"):
            dist = round((route_result.get("distance_m") or 0) / 1000, 1)
            mins = max(1, round((route_result.get("duration_sec") or 0) / 60)) if route_result.get("duration_sec") else "-"
            text = f"🍊 地图路线已生成：{' → '.join(route_result.get('waypoints') or [])}，约 {dist}km / {mins}min。可点击查看地图路线。"
        else:
            text = route_result.get("message") or route_result.get("error") or "⚠️ 地图路线暂未返回，已启用备用方案"
        yield f"data: {json.dumps({'type':'final','text':text}, ensure_ascii=False)}\n\n"
    return Response(stream_with_context(generate()), mimetype="text/event-stream",
                    headers={"Cache-Control":"no-cache","X-Accel-Buffering":"no"})

def _rule_confirm_order_response(user_message: str, user_id: str = "") -> Response:
    def generate():
        order_id = _extract_order_id(user_message)
        args = {"order_id": order_id}
        yield f"data: {json.dumps({'type':'step_start','id':1,'tool':'confirm_mock_order','input':args}, ensure_ascii=False)}\n\n"
        result = tool_confirm_mock_order(order_id, user_id)
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


def _looks_premium_rag_search(text: str) -> bool:
    return (
        _looks_black_pearl_intent(text)
        or _looks_michelin_intent(text)
        or _looks_generic_premium_dining(text)
    )


def _looks_weather_only_query(text: str) -> bool:
    s = re.sub(r"\[[^\]]*坐标[^\]]*\]", "", str(text or ""))
    if not re.search(r"天气|气温|几度|下雨|晴|阴|温度|湿度|风力|体感|weather", s, re.I):
        return False
    return not bool(re.search(r"行程|路线|规划|怎么玩|去哪|酒店|餐厅|美食|门票|高铁|飞机|打车|黑珍珠|米其林|团购", s))


def _weather_city_from_message(text: str, city_hint: str) -> str:
    s = str(text or "")
    city = extract_city_from_message(s) or _detect_message_destination(s) or city_hint or "上海"
    m1 = re.search(r"([^\s，,。！!？?]{2,12})(?:的|今天|明天|现在)?天气", s)
    if m1:
        raw = re.sub(r"[的是怎么样查询今天明天现在]", "", m1.group(1)).strip()
        if len(raw) >= 2 and not re.search(r"当前位置|当前定位|我这里|我在|附近|本地", raw):
            city = raw
    return _city_alias(_clean_place_token(city)) or "上海"


def _weather_final_text(result: dict) -> str:
    if not result.get("success"):
        return result.get("message") or result.get("error") or WEATHER_FRIENDLY_FALLBACK
    data = result.get("data") or {}
    city = result.get("city") or "当前位置"
    cache_note = "\n天气服务刚才较忙，已使用最近一次可用天气。" if result.get("stale") else ""
    return _clean_markdown(
        f"{city} · 实时天气\n"
        f"{data.get('text', '未知')}，{data.get('temp', '-')}℃，体感 {data.get('feels_like', '-')}℃。\n"
        f"湿度 {data.get('rh', '-')}%，{data.get('wind_dir', '')} {data.get('wind_class', '')}。\n"
        "天气只作为出行辅助：有雨优先室内/少骑行，高温注意补水，正常天气可按原路线出发。"
        f"{cache_note}"
    )


def _rule_weather_agent_response(user_message: str, city_hint: str) -> Response:
    def generate():
        coords = _parse_lat_lng(user_message)
        if coords:
            args = {"lat": coords["lat"], "lng": coords["lng"], "city": "当前位置"}
            yield f"data: {json.dumps({'type':'step_start','id':1,'tool':'get_weather','input':args}, ensure_ascii=False)}\n\n"
            result = tool_get_weather_by_coords(coords["lat"], coords["lng"], "当前位置")
        else:
            city = _weather_city_from_message(user_message, city_hint)
            args = {"city": city}
            yield f"data: {json.dumps({'type':'step_start','id':1,'tool':'get_weather','input':args}, ensure_ascii=False)}\n\n"
            result = tool_get_weather(city)
        yield f"data: {json.dumps({'type':'step_done','id':1,'tool':'get_weather','result':result,'summary':_tool_summary('get_weather', args, result)}, ensure_ascii=False)}\n\n"
        yield f"data: {json.dumps({'type':'final','text':_weather_final_text(result)}, ensure_ascii=False)}\n\n"
    return Response(stream_with_context(generate()), mimetype="text/event-stream",
                    headers={"Cache-Control":"no-cache","X-Accel-Buffering":"no"})


def _premium_rag_final_text(user_message: str, rag_result: dict, nearest_result: dict = None) -> str:
    city, _ = _premium_query_city_scope(user_message, "")
    section_title = "黑珍珠推荐" if _looks_black_pearl_intent(user_message) else "米其林推荐"
    source_label = os.path.basename(BLACK_PEARL_PDF_PATH) if _looks_black_pearl_intent(user_message) else os.path.basename(CSV_PATH)
    section = _premium_section(section_title, rag_result or {}, source_label)
    payload = _build_restaurant_recommendations_response(user_message, city, [section], nearest_result)
    return json.dumps(payload, ensure_ascii=False)


def _rule_premium_rag_agent_response(user_message: str, city_hint: str) -> Response:
    def generate():
        coords = _parse_lat_lng(user_message)
        wants_nearest = bool(re.search(r"附近|最近|离我|就近|nearby|near me", str(user_message or ""), re.I))
        wants_black_pearl = _looks_black_pearl_intent(user_message)
        wants_michelin = _looks_michelin_intent(user_message)
        wants_generic = _looks_generic_premium_dining(user_message)
        if wants_generic and not (wants_black_pearl or wants_michelin):
            wants_black_pearl = True
            wants_michelin = True
        target_city, explicit_city = _premium_query_city_scope(user_message, city_hint)
        rag_query = user_message if explicit_city or not target_city else f"{target_city} {user_message}"

        if wants_black_pearl and wants_michelin:
            print(f"[RULE_ROUTER] intent=premium_rag_first tool=premium_dining_rag nearest={wants_nearest} coords={bool(coords)}")
            bp_query = _premium_black_pearl_query(rag_query)
            bp_args = {"query": bp_query}
            yield f"data: {json.dumps({'type':'step_start','id':1,'tool':'search_black_pearl','input':bp_args}, ensure_ascii=False)}\n\n"
            bp_result = tool_search_black_pearl(bp_query)
            yield f"data: {json.dumps({'type':'step_done','id':1,'tool':'search_black_pearl','result':bp_result,'summary':_tool_summary('search_black_pearl', bp_args, bp_result)}, ensure_ascii=False)}\n\n"

            michelin_query = _premium_michelin_query(rag_query)
            michelin_args = {"query": michelin_query}
            yield f"data: {json.dumps({'type':'step_start','id':2,'tool':'search_michelin','input':michelin_args}, ensure_ascii=False)}\n\n"
            michelin_result = tool_search_local_michelin_rag(michelin_query)
            yield f"data: {json.dumps({'type':'step_done','id':2,'tool':'search_michelin','result':michelin_result,'summary':_tool_summary('search_michelin', michelin_args, michelin_result)}, ensure_ascii=False)}\n\n"

            nearest_result = None
            if wants_nearest and coords:
                n_args = {"lat": coords["lat"], "lng": coords["lng"], "limit": 5, "cuisine_filter": ""}
                yield f"data: {json.dumps({'type':'step_start','id':3,'tool':'find_nearest_michelin','input':n_args}, ensure_ascii=False)}\n\n"
                nearest_result = tool_find_nearest_michelin(coords["lat"], coords["lng"], 5, "")
                yield f"data: {json.dumps({'type':'step_done','id':3,'tool':'find_nearest_michelin','result':nearest_result,'summary':_tool_summary('find_nearest_michelin', n_args, nearest_result)}, ensure_ascii=False)}\n\n"

            bp_source = (
                f"{os.path.basename(BLACK_PEARL_SINGAPORE_XLSX_PATH)} / {os.path.basename(BLACK_PEARL_PDF_PATH)}"
                if re.search(r"新加坡|singapore", bp_query, re.I)
                else os.path.basename(BLACK_PEARL_PDF_PATH)
            )
            combined = {
                "message": "已整理出餐厅推荐，未使用 Mock 数据。",
                "query": rag_query,
                "city": target_city,
                "sections": [
                    _premium_section("黑珍珠知识库", bp_result, bp_source),
                    _premium_section("米其林知识库", michelin_result, os.path.basename(CSV_PATH)),
                ],
            }
            final_text = _premium_dining_final_text(combined, nearest_result)
            if wants_nearest and not coords:
                try:
                    payload = json.loads(final_text)
                    payload.setdefault("warnings", []).append("你问了最近/附近，但当前没有可用于距离计算的经纬度。")
                    final_text = json.dumps(payload, ensure_ascii=False)
                except Exception:
                    pass
            yield f"data: {json.dumps({'type':'final','text':final_text}, ensure_ascii=False)}\n\n"
            return

        tool = "search_black_pearl" if wants_black_pearl or not wants_michelin else "search_michelin"
        args = {"query": rag_query}
        print(f"[RULE_ROUTER] intent=premium_rag_first tool={tool} nearest={wants_nearest} coords={bool(coords)}")
        yield f"data: {json.dumps({'type':'step_start','id':1,'tool':tool,'input':args}, ensure_ascii=False)}\n\n"
        rag_result = tool_search_black_pearl(rag_query) if tool == "search_black_pearl" else tool_search_local_michelin_rag(rag_query)
        yield f"data: {json.dumps({'type':'step_done','id':1,'tool':tool,'result':rag_result,'summary':_tool_summary(tool, args, rag_result)}, ensure_ascii=False)}\n\n"

        nearest_result = None
        if wants_nearest and coords and wants_michelin and not wants_black_pearl:
            n_args = {"lat": coords["lat"], "lng": coords["lng"], "limit": 5, "cuisine_filter": ""}
            yield f"data: {json.dumps({'type':'step_start','id':2,'tool':'find_nearest_michelin','input':n_args}, ensure_ascii=False)}\n\n"
            nearest_result = tool_find_nearest_michelin(coords["lat"], coords["lng"], 5, "")
            yield f"data: {json.dumps({'type':'step_done','id':2,'tool':'find_nearest_michelin','result':nearest_result,'summary':_tool_summary('find_nearest_michelin', n_args, nearest_result)}, ensure_ascii=False)}\n\n"

        final_text = _premium_rag_final_text(rag_query, rag_result, nearest_result)
        yield f"data: {json.dumps({'type':'final','text':final_text}, ensure_ascii=False)}\n\n"
    return Response(stream_with_context(generate()), mimetype="text/event-stream",
                    headers={"Cache-Control":"no-cache","X-Accel-Buffering":"no"})


def run_deepseek_agent(user_message: str, city_hint: str = "上海",
                       history: list = None, persona: str = "",
                       route_profile: str = "", route_strategy: str = "",
                       map_provider: str = "", extra_system: str = "",
                       body_coords: dict = None, user_id: str = "",
                       session_id: str = "default") -> Response:
    user_id = _safe_user_id(user_id)
    _update_soul_memory_from_message(user_message)
    if _extract_order_id(user_message) and re.search(r"确认|下单|预订|就这个", user_message):
        print("[RULE_ROUTER] intent=mock_order_confirm")
        return _rule_confirm_order_response(user_message, user_id)
    if _looks_weather_only_query(user_message):
        print("[RULE_ROUTER] intent=weather_fast")
        return _rule_weather_agent_response(user_message, city_hint)
    if _looks_public_facility_search(user_message):
        print("[RULE_ROUTER] intent=public_facility_search -> amap_poi_only")
        return _rule_public_facility_agent_response(user_message, city_hint)
    if _looks_premium_rag_search(user_message):
        return _rule_premium_rag_agent_response(user_message, city_hint)
    if _looks_mock_resource_task(user_message):
        print("[RULE_ROUTER] intent=mock_order")
        return _rule_mock_resource_agent_response(user_message, city_hint, persona, map_provider, body_coords)
    if _looks_direct_amap_route(user_message):
        print("[RULE_ROUTER] intent=route_planning -> amap_route")
        return _rule_amap_route_response(user_message, city_hint)
    if _looks_direct_meituan_resource(user_message):
        print("[RULE_ROUTER] intent=food_or_hotel_search -> meituan_first")
        return _rule_meituan_resource_agent_response(user_message, city_hint)
    if _looks_meituan_trip(user_message):
        print("[RULE_ROUTER] intent=trip_plan -> planning_pipeline")
        return _rule_meituan_trip_agent_response(user_message, city_hint, persona, map_provider)
    if not _has_any_llm():
        if _looks_panorama_trip(user_message):
            return _mock_panorama_agent_response(user_message, city_hint, persona, map_provider)
        if _looks_weekend_trip(user_message):
            return _mock_weekend_agent_response(user_message, city_hint, persona,
                                                route_profile, map_provider)
        def _nk():
            yield f"data: {json.dumps({'type':'error','text':'请设置 DEEPSEEK_API_KEY 或 LONGCAT_API_KEY'}, ensure_ascii=False)}\n\n"
        return Response(stream_with_context(_nk()), mimetype="text/event-stream")

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
                _deepseek_t0 = time.perf_counter()
                resp = _llm_chat_completion({
                    "messages":msgs,
                    "tools":AGENT_TOOLS,"tool_choice":"auto",
                    "max_tokens":2000,"temperature":0.3}, purpose="agent_tool_loop")
                result = resp.json()
            except Exception as e:
                _record_tool_call("llm", "timeout" if "timeout" in str(e).lower() else "error", round((time.perf_counter() - _deepseek_t0) * 1000), purpose="agent_tool_loop")
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
                    elif fn == "search_black_pearl":
                        tr = tool_search_black_pearl(fa.get("query",""))
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
                        ride_req = dict(fa)
                        ride_req.setdefault("user_query", user_message)
                        ride_req.setdefault("userLocation", body_coords)
                        resolved_ride = _resolve_mock_taxi_request(ride_req, fa.get("city", city_hint), user_message)
                        tr = tool_mock_request_ride(
                            origin=resolved_ride.get("origin", ""),
                            destination=resolved_ride.get("destination", ""),
                            city=resolved_ride.get("city") or fa.get("city", city_hint),
                            trigger_reason=fa.get("trigger_reason", user_message),
                            user_context=resolved_ride.get("user_context", {}),
                        ) if resolved_ride.get("success") else resolved_ride
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
                    elif fn == "mock_book_train":
                        tr = tool_mock_book_train(
                            origin=fa.get("origin", ""),
                            destination=fa.get("destination", ""),
                            date=fa.get("date", ""),
                            seat_class=fa.get("seat_class", "二等座"),
                            passengers=int(fa.get("passengers", 1) or 1),
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
                            user_context={**fa.get("user_context", {}), "user_id": user_id, "session_id": session_id},
                        )
                    elif fn == "confirm_mock_order":
                        tr = tool_confirm_mock_order(fa.get("order_id", ""), user_id)
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
    lat = request.args.get("lat", "").strip()
    lng = request.args.get("lng", "").strip()
    if lat and lng:
        r = tool_get_weather_by_coords(lat, lng, request.args.get("city", "当前位置").strip() or "当前位置")
    else:
        r = tool_get_weather(request.args.get("city","上海").strip())
    if r.get("success"):
        return jsonify({
            "status": "success",
            "city": r["city"],
            "data": r["data"],
            "cached": bool(r.get("cached")),
            "stale": bool(r.get("stale")),
            "message": r.get("message", ""),
        })
    return jsonify({"status":"warning","message":r.get("message") or WEATHER_FRIENDLY_FALLBACK}), 200


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
    user_id = _request_user_id(b)
    session_id = b.get("session_id", "default")
    user_context = {**(b.get("user_context") or {}), "user_id": user_id, "session_id": session_id}
    r = tool_create_pending_order(
        order_type=b.get("order_type", "hotel"),
        item=b.get("item", {}),
        user_context=user_context,
    )
    return jsonify(r)


@app.route("/api/order/confirm_mock", methods=["POST"])
def api_confirm_mock_order():
    b = request.get_json(force=True)
    order_id = b.get("order_id", "")
    if not order_id:
        return jsonify({"success": False, "error": "order_id不能为空"}), 400
    r = tool_confirm_mock_order(order_id, _request_user_id(b))
    return jsonify(r)

@app.route("/api/mock/ride_quote", methods=["POST"])
def api_mock_ride_quote():
    b = request.get_json(force=True)
    resolved = _resolve_mock_taxi_request(b, b.get("city", ""), b.get("user_query") or b.get("trigger_reason") or "")
    if not resolved.get("success"):
        return jsonify(resolved), 400
    return jsonify(tool_mock_request_ride(
        origin=resolved["origin"],
        destination=resolved["destination"],
        city=resolved.get("city", ""),
        trigger_reason=b.get("trigger_reason", ""),
        user_context=resolved.get("user_context", {}),
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


@app.route("/api/mock/flight_order", methods=["POST"])
def api_mock_flight_order():
    b = request.get_json(force=True)
    if not b.get("flight"):
        origin = (b.get("origin") or b.get("from") or "").strip()
        destination = (b.get("destination") or b.get("to") or "").strip()
        if not origin:
            return jsonify({"success": False, "error": "出发地待确认，可选择：当前位置 / 上海 / 手动填写"}), 400
        print(f"[MOCK_FLIGHT_ORDER] origin={origin} destination={destination}", flush=True)
        return jsonify(tool_mock_search_flights(
            origin=origin,
            destination=destination,
            date=b.get("date", ""),
            budget=int(b.get("budget", 0) or 0),
            passengers=int(b.get("passengers", 1) or 1),
            cabin=b.get("cabin", "economy"),
            user_context=b.get("user_context", {}),
        ))
    print(f"[MOCK_FLIGHT_ORDER] flight={b.get('flight', {}).get('flight_no', '')}", flush=True)
    return jsonify(tool_mock_create_flight_order(
        flight=b.get("flight", {}),
        user_context=b.get("user_context", {}),
    ))


# ── 行程方案按钮：确定动作接口（按钮→真实动作，不再回灌 /api/agent） ──────────
def _mock_hotel_list(city: str, price_high=None) -> list:
    preset = RESOURCE_BOOKING_PRESET["hotel"]
    cap = int(price_high) if price_high else preset["high"]
    cap = max(preset["low"] + 60, cap)
    out = []
    for i, name in enumerate(preset["names"][:3]):
        seed = f"{city}|hotellist|{i}"
        price = min(cap, _mock_int(seed + "p", preset["low"], cap))
        out.append({
            "name": f"{city}{name}", "cost": price, "price": price,
            "rating": str(round(4.3 + _mock_int(seed + "r", 0, 6) / 10, 1)),
            "address": f"{city}{preset['spot'][i % len(preset['spot'])]}",
        })
    return out


@app.route("/api/amap/route_link", methods=["POST", "OPTIONS"])
def api_amap_route_link():
    if request.method == "OPTIONS":
        return ("", 204)
    b = request.get_json(force=True)
    city = (b.get("city") or "上海").strip()
    pts = [str(p).strip() for p in (b.get("route_points") or b.get("waypoints") or []) if p]
    print(f"[AMAP_ROUTE_LINK] city={city} points={pts}", flush=True)
    if len(pts) >= 2:
        return jsonify({"success": True, "map_url": _amap_map_url_for_route(pts, city), "source": "amap"})
    # 兜底：路线点不足也不报错，给高德搜索/导航入口
    target = pts[0] if pts else city
    return jsonify({"success": True, "map_url": f"https://www.amap.com/search?query={quote(target)}",
                    "source": "amap_search", "note": "路线节点不足，已生成高德搜索链接"})


@app.route("/api/action/search_hotel", methods=["POST", "OPTIONS"])
def api_action_search_hotel():
    if request.method == "OPTIONS":
        return ("", 204)
    b = request.get_json(force=True)
    city = (b.get("city") or "上海").strip()
    keyword = (b.get("keyword") or "平价酒店").strip()
    price_high = b.get("price_high")
    print(f"[ACTION_SEARCH_HOTEL] city={city} keyword={keyword} price_high={price_high}", flush=True)
    filters = {"price_high": price_high} if price_high else {}
    hotels, source = [], ""
    # Layer1: 美团 Skill / 龙猫
    try:
        r = tool_call_meituan_skill("hotel_search", city, keyword, "", None, None, filters, 3)
        if r.get("success") and r.get("results"):
            hotels = r["results"]
            source = r.get("source", "meituan_skill")
    except Exception as e:
        print(f"[search_hotel] meituan skill failed: {e}")
    # Layer2: 高德 POI 备用
    if not hotels:
        try:
            items = search_amap_place(keyword, city, 3) or []
            hotels = [{"name": it.get("name", ""), "address": it.get("address", ""),
                       "cost": "", "rating": str(it.get("rating", ""))} for it in items if it.get("name")]
            if hotels:
                source = "amap_poi"
        except Exception as e:
            print(f"[search_hotel] amap poi failed: {e}")
    # Layer3: Mock 兜底
    if not hotels:
        hotels = _mock_hotel_list(city, price_high)
        source = "mock_fallback"
    return jsonify({"success": True, "city": city, "keyword": keyword,
                    "hotels": hotels[:3], "source": source})


@app.route("/api/mock/taxi_order", methods=["POST", "OPTIONS"])
def api_mock_taxi_order():
    if request.method == "OPTIONS":
        return ("", 204)
    b = request.get_json(force=True)
    resolved = _resolve_mock_taxi_request(b, b.get("city", ""), b.get("user_query") or "")
    if not resolved.get("success"):
        print(f"[MOCK_TAXI_ORDER] unresolved error={resolved.get('error')}", flush=True)
        return jsonify(resolved), 400
    frm = resolved["origin"]
    to = resolved["destination"]
    city = (resolved.get("city") or "").strip()
    print(f"[MOCK_TAXI_ORDER] city={city} from={frm} to={to}", flush=True)
    ride = tool_mock_request_ride(origin=frm, destination=to, city=city,
                                  trigger_reason=b.get("user_query") or "按钮一键打车",
                                  user_context=resolved.get("user_context", {}))
    if not ride.get("success", True):
        return jsonify(ride), 400
    q = ride.get("quote", {})
    order_id = "MDCG-TAXI-" + uuid.uuid4().hex[:8].upper()
    return jsonify({
        "success": True, "order_id": order_id,
        "from": frm, "to": to, "city": city,
        "destination_place": resolved.get("destination_place") or {},
        "estimated_price": q.get("price_estimate"),
        "estimated_duration": f"{q.get('eta_minutes', '-')}min",
        "status": "mock_order_success",
        "message": f"🚕 Mock 打车成功，订单号 {order_id}",
        "note": "Mock 预订，仅用于黑客松端到端演示。",
    })


@app.route("/api/mock/train_order", methods=["POST", "OPTIONS"])
def api_mock_train_order():
    if request.method == "OPTIONS":
        return ("", 204)
    b = request.get_json(force=True)
    origin = b.get("from") or b.get("origin", "")
    destination = b.get("to") or b.get("destination", "")
    if not str(origin or "").strip():
        return jsonify({"success": False, "error": "出发地待确认，可选择：当前位置 / 上海 / 手动填写"}), 400
    print(f"[MOCK_TRAIN_ORDER] origin={origin} destination={destination}", flush=True)
    result = tool_mock_book_train(
        origin=origin,
        destination=destination,
        date=b.get("date", ""),
        seat_class=b.get("seat_class", "二等座"),
        passengers=int(b.get("passengers", 1) or 1),
        user_context=b.get("user_context", {}),
    )
    seat = b.get("seat_class", "二等座")
    order_id = "MDCG-TRAIN-" + uuid.uuid4().hex[:4].upper()
    train = dict(result.get("train") or {})
    train.update({
        "train_no": "G-MOCK-" + str(_mock_int(f"{origin}|{destination}|train", 1000, 9999)),
        "origin": origin,
        "destination": destination or train.get("destination") or "目的地",
        "depart_time": "09:20",
        "arrive_time": "10:15",
        "duration": "55min",
        "seat": seat,
        "seat_class": seat,
        "price": 73,
    })
    result.update({
        "success": True,
        "order_id": order_id,
        "status": "pending_confirm",
        "train_no": train["train_no"],
        "origin": train["origin"],
        "destination": train["destination"],
        "depart_time": train["depart_time"],
        "arrive_time": train["arrive_time"],
        "duration": train["duration"],
        "seat": seat,
        "price": train["price"],
        "message": "Mock 高铁待确认订单已生成，仅用于黑客松演示。",
        "train": train,
    })
    return jsonify(result)


@app.route("/api/mock/hotel_order", methods=["POST", "OPTIONS"])
def api_mock_hotel_order():
    if request.method == "OPTIONS":
        return ("", 204)
    b = request.get_json(force=True)
    city = (b.get("city") or "上海").strip()
    keyword = b.get("hotel_name") or b.get("keyword", "")
    print(f"[MOCK_HOTEL_ORDER] city={city} keyword={keyword}", flush=True)
    return jsonify(tool_mock_book_resource(
        booking_kind="hotel",
        city=city,
        keyword=keyword,
        user_context=b.get("user_context", {}),
    ))


@app.route("/api/mock/restaurant_booking", methods=["POST", "OPTIONS"])
def api_mock_restaurant_booking():
    if request.method == "OPTIONS":
        return ("", 204)
    b = request.get_json(force=True)
    city = (b.get("city") or "上海").strip()
    keyword = b.get("restaurant_name") or b.get("selected_place") or b.get("keyword", "")
    print(f"[MOCK_RESTAURANT_ORDER] city={city} keyword={keyword}", flush=True)
    return jsonify(tool_mock_book_resource(
        booking_kind="restaurant",
        city=city,
        keyword=keyword,
        user_context=b.get("user_context", {}),
    ))


@app.route("/api/mock/ticket_order", methods=["POST", "OPTIONS"])
def api_mock_ticket_order():
    if request.method == "OPTIONS":
        return ("", 204)
    b = request.get_json(force=True)
    city = (b.get("city") or "上海").strip()
    keyword = b.get("spot_name") or b.get("keyword", "")
    print(f"[MOCK_TICKET_ORDER] city={city} keyword={keyword}", flush=True)
    return jsonify(tool_mock_book_resource(
        booking_kind="ticket",
        city=city,
        keyword=keyword,
        user_context=b.get("user_context", {}),
    ))


@app.route("/api/mock/queue_monitor", methods=["POST", "OPTIONS"])
def api_mock_queue_monitor():
    if request.method == "OPTIONS":
        return ("", 204)
    b = request.get_json(force=True)
    city = (b.get("city") or "上海").strip()
    target = b.get("target") or b.get("target_name") or b.get("selected_place") or b.get("keyword") or "热门餐厅"
    print(f"[MOCK_QUEUE_MONITOR] city={city} target={target}", flush=True)
    return jsonify(tool_mock_start_service_monitor(
        resource_type="queue",
        target_name=target,
        city=city,
        condition=b.get("condition", "排队低于10分钟时提醒"),
        callback_action=b.get("callback_action", "有位或低排队时提醒，可切换备选"),
        duration_minutes=int(b.get("duration_minutes") or b.get("threshold_minutes") or 30),
        user_context=b.get("user_context", {}),
    ))


@app.route("/api/action/adjust_plan", methods=["POST", "OPTIONS"])
def api_action_adjust_plan():
    if request.method == "OPTIONS":
        return ("", 204)
    b = request.get_json(force=True)
    mode = (b.get("mode") or "").strip()
    labels = {"cheaper": "更省钱", "relax": "更松弛", "special_force": "特种兵"}
    print(f"[ADJUST_PLAN] mode={mode}", flush=True)
    return jsonify({
        "success": True,
        "mode": mode,
        "message": f"已切换为{labels.get(mode, '新的')}方案偏好，继续规划时会按该模式调整。",
    })


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
            "desc": "该风格方案暂不可用，请优先查看 DeepSeek 路线地图卡。",
            "budget_total": budget,
            "days": [],
            "error": f"{city}松弛感方案生成失败，未使用模板路线。",
        },
        {
            "persona_key": "special_force",
            "label": "⚡ 特种兵模式",
            "desc": "该风格方案暂不可用，请优先查看 DeepSeek 路线地图卡。",
            "budget_total": budget + 120,
            "days": [],
            "error": f"{city}特种兵方案生成失败，未使用模板路线。",
        },
        {
            "persona_key": "foodie",
            "label": "🍜 美食脑袋",
            "desc": "该风格方案暂不可用，请优先查看 DeepSeek 路线地图卡。",
            "budget_total": budget + 180,
            "days": [],
            "error": f"{city}美食方案生成失败，未使用模板路线。",
        },
    ]

@app.route("/api/trip_compare", methods=["POST", "OPTIONS"])
@app.route("/api/plan_variants", methods=["POST", "OPTIONS"])
def api_trip_compare():
    """生成3种人格方案供用户对比选择。"""
    if request.method == "OPTIONS":
        return jsonify({"ok": True})
    b = request.get_json(force=True, silent=True) or {}
    request_city = (b.get("city") or "上海").strip()
    user_prompt = (b.get("user_prompt") or b.get("prompt") or f"去{request_city}玩").strip()
    body_coords = (
        _extract_coord_pair({"lat": b.get("lat"), "lng": b.get("lng")})
        or _extract_coord_pair({"lat": b.get("latitude"), "lng": b.get("longitude")})
        or _extract_coord_pair(b.get("userLocation"))
        or _extract_coord_pair(b.get("location"))
    )
    _, city, city_source = _resolve_agent_city_for_route_card(user_prompt, request_city, {}, body_coords)
    print(f"[TRIP_COMPARE_CITY] city={city} source={city_source} coords={bool(body_coords)}")
    budget = _optional_int(b.get("budget"), None) or _extract_trip_requirements(user_prompt, city).get("budget", 800)

    # 3种对比人格：松弛 / 特种兵 / 美食脑袋
    compare_personas = [
        {"key": "relax",        "label": "🍃 松弛慢游",   "desc": "少景点多停留，保留大量弹性时间"},
        {"key": "special_force","label": "⚡ 特种兵模式", "desc": "高密度打卡，效率最大化"},
        {"key": "foodie",       "label": "🍜 美食脑袋",   "desc": "以美食为主线，景点顺路打卡"},
    ]

    try:
        req0 = _extract_trip_requirements(user_prompt, city)
        dest = _resolve_place_info(req0.get("destination") or city, city)
        cname = dest.get("name") or city
        days_n = max(1, int(req0.get("days") or 1))
        # 真实候选点：一次获取、禁跨城；只用真实地图 POI，不用任何模板
        raw = (search_amap_place("景点 景区 公园 博物馆 地标", cname, 8) or []) + (search_amap_place("美食 本地菜 餐厅", cname, 8) or [])
        seen, cand = set(), []
        for x in raw:
            n = _norm_place_name(x.get("name"))
            if n and n not in seen:
                seen.add(n); cand.append(x)
        nondining = [x for x in cand if not _is_dining_candidate(x)]
        dining = [x for x in cand if _is_dining_candidate(x)]
        cfg = {
            "relax":         {"nd": 3, "din": 1, "stay": 110, "intensity": "低", "best": "想轻松玩、不赶路的人"},
            "special_force": {"nd": 4, "din": 2, "stay": 55,  "intensity": "高", "best": "想多打卡、效率优先的人"},
            "foodie":        {"nd": 2, "din": 2, "stay": 75,  "intensity": "中", "best": "想吃好一点的人"},
        }
        def _variant(meta):
            pk = meta["key"]; c = cfg[pk]
            base = {"persona_key": pk, "label": meta["label"], "desc": meta["desc"]}
            if len(nondining) < 2:
                return {**base, "days": [], "error": f"{cname}可验证景点不足，为避免模板路线暂不生成该方案。"}
            nd, din = nondining[:c["nd"]], dining[:c["din"]]
            seq = []
            if nd: seq.append((nd[0], "09:30", "sight"))
            if din: seq.append((din[0], "12:00", "food"))
            for j, x in enumerate(nd[1:], 1):
                seq.append((x, ["14:30", "16:00", "17:00"][min(j - 1, 2)], "sight"))
            if len(din) > 1: seq.append((din[1], "18:30", "food"))
            seq = seq[:6]
            rm = [{"name": x.get("name"), "type": ("\u9910\u996e" if ty == "food" else "\u666f\u70b9"), "is_real_poi": True} for x, _, ty in seq]
            ok, _r = validate_route_quality(rm, pk == "foodie")
            if not ok:
                return {**base, "days": [], "error": "候选点质量不足，为避免模板路线暂不生成该方案。"}
            schedule = [{"time": t, "type": ty, "activity": x.get("name"), "duration_min": c["stay"]} for x, t, ty in seq]
            route = [x.get("name") for x, _, _ in seq]
            bud = _adjust_budget_by_persona(_budget_breakdown(budget, days_n, 0, False), _persona_state(pk))
            day = {"day": 1, "theme": meta["label"].split(" ")[-1], "route": route, "schedule": schedule,
                   "transport": "\u5730\u94c1/\u6253\u8f66 + \u6b65\u884c", "budget": bud.get("total"), "tip": c["best"]}
            return {**base, "days": [day], "budget_total": bud.get("total"),
                    "route_intensity": c["intensity"], "best_for": c["best"], "route_points": route}
        plans = [_variant(p) for p in compare_personas]
        if not any(p.get("days") for p in plans):
            return jsonify({"success": True, "city": city, "plans": _fallback_trip_compare_plans(city, budget),
                            "message": f"{cname}真实候选点不足，未生成模板对比方案。"})
        return jsonify({"success": True, "city": city, "plans": plans})
    except Exception as e:
        return jsonify({"success": True, "city": city,
                        "plans": _fallback_trip_compare_plans(city, budget),
                        "fallback": True,
                        "message": f"对比方案生成失败：{_safe_error_text(e)}"})


@app.route("/api/task-state", methods=["GET", "DELETE"])
def api_task_state():
    session_id = request.args.get("session_id", "default")
    user_id = _request_user_id({})
    state_session_id = _scoped_session_id(session_id, user_id)
    if request.method == "DELETE":
        _clear_task_state(state_session_id)
        return jsonify({"success": True})
    return jsonify(_get_task_state(state_session_id))


@app.route("/api/reset", methods=["POST"])
def api_reset():
    """完整清空指定 session 的所有后端状态，配合前端生成新 session_id 使用。"""
    b = request.get_json(force=True) or {}
    raw_session_id = b.get("session_id", "default")
    user_id = _request_user_id(b)
    session_id = _scoped_session_id(raw_session_id, user_id)
    _clear_task_state(session_id)
    print(f"[RESET] user_id={user_id!r} session {raw_session_id!r} cleared")
    return jsonify({"ok": True, "message": "session reset", "session_id": raw_session_id})


@app.route("/api/agent", methods=["POST"])
def api_agent():
    b          = request.get_json(force=True)
    msg        = b.get("message","").strip()
    request_city = b.get("city","上海").strip()
    city       = request_city
    raw_history= b.get("history", [])
    persona    = b.get("persona","").strip()
    personas   = b.get("personas", [])
    raw_session_id = b.get("session_id", "default")
    user_id = _request_user_id(b)
    session_id = _scoped_session_id(raw_session_id, user_id)
    action_type= b.get("action_type","").strip()
    option_id  = b.get("option_id","").strip()
    request_budget = _optional_int(b.get("budget"), 0) or 0
    request_people = _optional_int(b.get("people_count"), 0) or 0
    request_date = str(b.get("travel_date") or "").strip()
    request_budget_strategy = str(b.get("budget_strategy") or (_budget_strategy(request_budget) if request_budget else "")).strip()
    if isinstance(personas, list) and personas:
        merged = [persona] if persona else []
        merged.extend([str(x) for x in personas if x])
        persona = ",".join(dict.fromkeys([x for x in merged if x]))
    route_profile  = b.get("route_profile","").strip()
    route_strategy = b.get("route_strategy","").strip()
    map_provider   = b.get("map_provider","").strip()
    if not msg: return jsonify({"error":"message不能为空"}), 400
    body_coords = (
        _extract_coord_pair({"lat": b.get("lat"), "lng": b.get("lng")})
        or _extract_coord_pair({"lat": b.get("latitude"), "lng": b.get("longitude")})
        or _extract_coord_pair(b.get("userLocation"))
        or _extract_coord_pair(b.get("location"))
    )
    if body_coords and _looks_public_facility_search(msg) and not _parse_lat_lng(msg):
        msg = f"{msg}（我的当前位置：纬度{body_coords['lat']:.6f},经度{body_coords['lng']:.6f}）"
    hard_constraints = []
    if request_date:
        hard_constraints.append(f"出行日期{request_date}")
    if request_people:
        hard_constraints.append(f"出行人数{request_people}人")
    if request_budget:
        hard_constraints.append(f"预算{request_budget}元")
        hard_constraints.append(f"预算策略{request_budget_strategy or _budget_strategy(request_budget)}")
    if hard_constraints and "[任务硬约束]" not in msg:
        msg = f"{msg}\n\n[任务硬约束] " + "；".join(hard_constraints)

    # ── 要求10：详细调试日志 ────────────────────────────────────────
    ts_before = _get_task_state(session_id)
    detected_city = extract_city_from_message(msg)
    is_new_task = detect_new_task(msg)
    is_pure_reset = is_pure_reset_command(msg) and not is_new_task
    _det_city_str, final_city_used, city_source = _resolve_agent_city_for_route_card(msg, request_city, ts_before, body_coords)
    if detected_city:
        _det_city_str = detected_city
        final_city_used = detected_city
        city_source = "explicit_destination"
    is_new_destination_task = _is_new_destination_task(msg, _det_city_str)
    print(f"[AGENT] user_id={user_id!r} raw_session={raw_session_id!r}")
    print(f"[AGENT] raw_message={msg!r}")
    print(f"[AGENT] is_pure_reset={is_pure_reset}")
    print(f"[AGENT] detected_city={_det_city_str!r}")
    print(f"[AGENT] is_new_task={is_new_task}")
    print(f"[AGENT] is_new_destination_task={is_new_destination_task}")
    print(f"[AGENT] request_city={request_city!r}")
    print(f"[AGENT] city_source={city_source!r} body_coords={bool(body_coords)}")
    print(f"[AGENT] task_state_before={ts_before}")
    if is_pure_reset:
        _clear_task_state(session_id)
        print("[AGENT] planning_pipeline_called=False")
        def _reset_stream():
            yield f"data: {json.dumps({'type':'final','text':'🍊 已重置，请告诉我新需求。','task_state':{}}, ensure_ascii=False)}\n\n"
        return Response(stream_with_context(_reset_stream()), mimetype="text/event-stream")
    city = final_city_used
    _is_fw = msg.strip() in _FOLLOWUP_SET
    _is_nt = is_new_task or _is_new_task(msg, ts_before)
    print(f"[AGENT] task_state_before.city={(ts_before.get('city') or ts_before.get('active_city') or ts_before.get('destination') or ts_before.get('active_destination'))!r}")
    print(f"[AGENT] final_city_used={final_city_used!r} | is_new_task={_is_nt} | is_followup={_is_fw}")
    print(f"[AGENT] current_task_before: city={ts_before.get('active_city')!r} status={ts_before.get('status','idle')} goal={ts_before.get('last_user_goal','')[:40]!r}")

    # ══ 第一步：新任务检测（优先于短回复解析，避免被误判成重置） ═══════
    is_followup = False
    if (_is_nt or is_new_destination_task) and not is_followup:
        _clear_task_state(session_id)
        if is_new_destination_task:
            intent = _extract_trip_requirements(msg, final_city_used)
            intent["destination"] = final_city_used
            intent["persona"] = persona
            if request_budget:
                intent["budget"] = request_budget
            create_task_from_intent(session_id, intent)
        print(f"[AGENT] new task detected, cleared state and will continue planning")

    # ══ 第二步：短输入解析器（只处理非新任务的选择/确认/纯重置） ════════
    if not (_is_nt or is_new_destination_task):
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

    # ══ 第三步：当前输入城市立即锁定到 task_state ════════════════
    ts_now = _get_task_state(session_id)
    if final_city_used:
        _prev_city = ts_now.get("active_city", "")
        if final_city_used != _prev_city:
            print(f"[AGENT] city lock: {_prev_city!r} → {final_city_used!r}")
        ts_now = dict(ts_now)
        ts_now["active_city"] = final_city_used
        ts_now["active_destination"] = final_city_used
        ts_now["city"] = final_city_used
        ts_now["destination"] = final_city_used
        if not ts_now.get("active_task_id"):
            ts_now["active_task_id"] = f"task_{uuid.uuid4().hex[:8]}"
        # 顺带提取预算/天数（要求1）
        _b_m = re.search(r"预算\s*([0-9]+)", msg)
        _d_m = re.search(r"([0-9一二两三四五六七八九十]{1,3})\s*天", msg)
        if _b_m:
            ts_now["active_budget"] = int(_b_m.group(1))
        if request_budget:
            ts_now["active_budget"] = request_budget
            ts_now["budget"] = request_budget
            ts_now["budget_strategy"] = request_budget_strategy or _budget_strategy(request_budget)
        if _d_m:
            ts_now["active_days"] = _zh_to_int(_d_m.group(1), 1)
        if request_people:
            ts_now["people_count"] = request_people
        if request_date:
            ts_now["travel_date"] = request_date
        if persona:
            ts_now["active_persona"] = persona
        _set_task_state(session_id, ts_now)
    print(f"[AGENT] task_state_after={_get_task_state(session_id)}")

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
            f"- 预算策略: {ts_now.get('budget_strategy','待定')}\n"
            f"- 出行人数: {ts_now.get('people_count','待定')}\n"
            f"- 出行日期: {ts_now.get('travel_date','待定')}\n"
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
                        if (evt.get("payload") or {}).get("reply_type") == "nearby_toilet_results":
                            payload = evt.get("payload") or {}
                            loc = payload.get("location") or {}
                            loc_city = ""
                            if loc.get("lat") is not None and loc.get("lng") is not None:
                                loc_city = _nearest_city_from_coords(float(loc["lat"]), float(loc["lng"]), "")
                            new_ts = {
                                "status": "awaiting_choice",
                                "active_intent": "nearby_toilet_finder",
                                "active_city": loc_city or "当前位置",
                                "active_destination": loc_city or "当前位置",
                                "city": loc_city or "当前位置",
                                "destination": loc_city or "当前位置",
                                "last_user_goal": msg,
                                "toilet_location": loc,
                                "updated_at": time.time(),
                            }
                            _set_task_state(session_id, new_ts)
                            evt["task_state"] = new_ts
                            print(f"[AGENT] final ts_status={new_ts.get('status')} intent=nearby_toilet_finder")
                            yield f"data: {json.dumps(evt, ensure_ascii=False)}\n\n"
                            continue
                        _agent_opts = (evt.get("task_state") or {}).get("options")
                        new_ts = _update_task_state_from_reply(session_id, msg, evt.get("text",""))
                        if _agent_opts:  # 保留即时工具(如找厕所)自带的兜底按钮，避免被任务状态覆盖
                            new_ts = dict(new_ts)
                            new_ts["options"] = _agent_opts
                        evt["task_state"] = new_ts
                        print(f"[AGENT] final ts_status={new_ts.get('status')} options={len(new_ts.get('last_options',[]))}")
                        yield f"data: {json.dumps(evt, ensure_ascii=False)}\n\n"
                        continue
                    if evt.get("type") == "step_done" and isinstance(evt.get("result"), dict):
                        result = evt["result"]
                        if result.get("type") in ("independent_trip_plan", "meituan_trip_plan") or evt.get("tool") in ("independent_trip_planner", "plan_meituan_trip"):
                            result["city"] = final_city_used or result.get("city") or result.get("destination", {}).get("name", "")
                            result["render_city"] = result["city"]
                            if isinstance(result.get("requirements"), dict) and result["city"]:
                                result["requirements"]["destination"] = result["city"]
                            if isinstance(result.get("route_card"), dict) and result["city"]:
                                result["route_card"]["city"] = result["city"]
                                if not result["route_card"].get("title"):
                                    days = result.get("requirements", {}).get("days", 1) if isinstance(result.get("requirements"), dict) else 1
                                    day_label = "1日" if int(days or 1) == 1 else f"{int(days or 1)}天"
                                    result["route_card"]["title"] = f"{result['city']}{day_label}行程规划"
                            title = str(result.get("title") or "")
                            if result["city"] and title and any(c in title and c != result["city"] for c in CITY_GEO_INDEX):
                                result["title"] = re.sub(_CITY_PAT, result["city"], title, count=1)
                            elif result["city"] and not title:
                                days = result.get("requirements", {}).get("days", 1) if isinstance(result.get("requirements"), dict) else 1
                                day_label = "1日" if int(days or 1) == 1 else f"{int(days or 1)}天"
                                result["title"] = f"{result['city']}{day_label}行程规划"
                            print(f"[AGENT] plan.city={result.get('city')!r}")
                            print(f"[AGENT] render_city={result.get('render_city')!r}")
                            yield f"data: {json.dumps(evt, ensure_ascii=False)}\n\n"
                            continue
                except Exception:
                    pass
            yield chunk

    base = run_deepseek_agent(msg, city, history, persona, route_profile,
                              route_strategy, map_provider, extra_system=task_ctx,
                              body_coords=body_coords, user_id=user_id,
                              session_id=raw_session_id)
    print("[AGENT] planning_pipeline_called=True")
    return Response(stream_with_context(_wrap_with_task_state(base.response)),
                    mimetype="text/event-stream")


@app.route("/api/chat", methods=["POST"])
def api_chat():
    if not _has_any_llm(): return jsonify({"error":"请设置 DEEPSEEK_API_KEY 或 LONGCAT_API_KEY"}), 500
    b          = request.get_json(force=True)
    msg        = b.get("message","").strip()
    city       = b.get("city","上海").strip()
    raw_history= b.get("history", [])
    persona    = b.get("persona","").strip()
    route_profile  = b.get("route_profile","").strip()
    route_strategy = b.get("route_strategy","").strip()
    map_provider   = b.get("map_provider","").strip()
    raw_session_id = b.get("session_id", "default")
    user_id = _request_user_id(b)
    session_id = _scoped_session_id(raw_session_id, user_id)
    action_type= b.get("action_type","").strip()
    option_id  = b.get("option_id","").strip()
    if not msg: return jsonify({"error":"message不能为空"}), 400

    # ── 日志 ──────────────────────────────────────────────────
    ts_before = _get_task_state(session_id)
    print(f"[CHAT] raw={msg!r} action_type={action_type!r} option_id={option_id!r} "
          f"status={ts_before.get('status','idle')} user_id={user_id} session={raw_session_id}")

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
            resp = _llm_chat_completion({
                "messages":msgs,"tools":AGENT_TOOLS,
                "tool_choice":"auto","max_tokens":1500,"temperature":0.3}, purpose="chat_tool_loop")
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
                elif fn=="search_black_pearl":    tr=tool_search_black_pearl(fa.get("query",""))
                elif fn=="call_meituan_skill":    tr=tool_call_meituan_skill(fa.get("intent","restaurant_search"),fa.get("city",city),fa.get("keyword",""),fa.get("location",""),fa.get("user_lat"),fa.get("user_lng"),fa.get("filters",{}),int(fa.get("limit",5)))
                elif fn=="find_nearest_michelin": tr=tool_find_nearest_michelin(float(fa.get("lat",0)),float(fa.get("lng",0)))
                elif fn=="mock_request_ride":
                    resolved_ride = _resolve_mock_taxi_request({**fa, "user_query": msg}, fa.get("city", city), msg)
                    tr = tool_mock_request_ride(
                        resolved_ride.get("origin", ""),
                        resolved_ride.get("destination", ""),
                        resolved_ride.get("city") or fa.get("city", city),
                        fa.get("trigger_reason", msg),
                        resolved_ride.get("user_context", {}),
                    ) if resolved_ride.get("success") else resolved_ride
                elif fn=="mock_search_flights":   tr=tool_mock_search_flights(fa.get("origin",""),fa.get("destination",""),fa.get("date",""),int(fa.get("budget",0) or 0),int(fa.get("passengers",1) or 1),fa.get("cabin","economy"),fa.get("user_context",{}))
                elif fn=="mock_book_train":       tr=tool_mock_book_train(fa.get("origin",""),fa.get("destination",""),fa.get("date",""),fa.get("seat_class","二等座"),int(fa.get("passengers",1) or 1),fa.get("user_context",{}))
                elif fn=="mock_start_service_monitor": tr=tool_mock_start_service_monitor(fa.get("resource_type","queue"),fa.get("target_name",""),fa.get("city",city),fa.get("condition",msg),fa.get("callback_action",""),int(fa.get("duration_minutes",30) or 30),fa.get("user_context",{}))
                elif fn=="mock_get_monitor_status": tr=tool_mock_get_monitor_status(fa.get("monitor_id",""))
                elif fn=="create_pending_order":  tr=tool_create_pending_order(fa.get("order_type","unknown"),fa.get("item",{}),{**fa.get("user_context",{}), "user_id": user_id, "session_id": raw_session_id})
                elif fn=="confirm_mock_order":    tr=tool_confirm_mock_order(fa.get("order_id",""), user_id)
                elif fn=="simulate_price_scenario": tr=tool_simulate_price_scenario(fa.get("event_type","normal"),fa.get("origin",""),fa.get("destination",""),fa.get("city",city))
                elif fn=="patch_plan_item":        tr=tool_patch_plan_item(fa.get("order_id",""),fa.get("item_type","hotel"),fa.get("reason",""),fa.get("persona",persona),fa.get("budget_max",0))
                else: tr={"error":"unknown"}
                msgs.append({"role":"tool","tool_call_id":tc["id"],"content":json.dumps(tr,ensure_ascii=False)})

    if not final_reply:
        try:
            resp2 = _llm_chat_completion({
                "messages":msgs,"max_tokens":1500,"temperature":0.3}, purpose="chat_final")
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
        payload = request.get_json(silent=True) or {}
        user_id = _request_user_id(payload)
        with _history_conn() as conn:
            conn.execute("DELETE FROM chat_messages WHERE user_id = ?", (user_id,))
            try:
                conn.execute("INSERT INTO chat_messages_fts(chat_messages_fts) VALUES('rebuild')")
            except Exception:
                pass
        return jsonify({"success": True, "user_id": user_id})
    if request.method == "GET":
        q = request.args.get("q", "").strip()
        limit = _optional_int(request.args.get("limit"), 30) or 30
        user_id = _request_user_id({})
        return jsonify({"success": True, "items": _search_history(q, limit, user_id), "user_id": user_id})
    b = request.get_json(force=True)
    messages = b.get("messages")
    city = b.get("city", "")
    persona = b.get("persona", "")
    session_id = b.get("session_id", "default")
    user_id = _request_user_id(b)
    lang = b.get("lang", "zh")
    saved = []
    if isinstance(messages, list):
        for msg in messages:
            if isinstance(msg, dict):
                item = _save_history_message(
                    msg.get("role", "assistant"),
                    msg.get("content", ""),
                    city, persona, session_id, lang,
                    msg.get("message_type", "text"),
                    msg.get("plan_json"),
                    msg.get("order_json"),
                    msg.get("meta_json"),
                    user_id,
                )
                if item:
                    saved.append(item)
    else:
        item = _save_history_message(
            b.get("role", "assistant"),
            b.get("content", ""),
            city, persona, session_id, lang,
            b.get("message_type", "text"),
            b.get("plan_json"),
            b.get("order_json"),
            b.get("meta_json"),
            user_id,
        )
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


@app.route("/ask_black_pearl", methods=["POST"])
def ask_black_pearl_route():
    b = request.get_json(force=True)
    q = b.get("question","").strip()
    if not q: return jsonify({"error":"问题不能为空"}), 400
    r = tool_search_black_pearl(q)
    if r.get("success"):
        return jsonify({
            "answer": _clean_markdown(r.get("answer","")),
            "references": r.get("references", []),
            "fallback": r.get("fallback", False),
            "source": r.get("source", BLACK_PEARL_PDF_PATH),
        })
    return jsonify({"error":r.get("error","黑珍珠PDF查询失败")}), 500


@app.route("/api/rag/premium_dining", methods=["POST"])
def api_premium_dining_rag():
    b = request.get_json(force=True) or {}
    q = str(b.get("question") or b.get("query") or "").strip()
    city = str(b.get("city") or "").strip()
    if not q:
        q = "黑珍珠 米其林 高端餐饮推荐"
    r = tool_search_premium_dining(q, city)
    return jsonify(r), (200 if r.get("success") else 500)


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


@app.route("/api/map/runtime_config", methods=["GET"])
def api_map_runtime_config():
    remote = request.headers.get("X-Forwarded-For", request.remote_addr or "").split(",")[0].strip()
    local_request = remote in ("127.0.0.1", "::1", "localhost")
    expose_js_keys = local_request or EXPOSE_MAP_JS_KEYS
    return jsonify({
        "success": True,
        "provider_priority": ["gaode", "baidu", "google"],
        "amap": {
            "jsapi_available": bool(AMAP_JSAPI_KEY) and expose_js_keys,
            "jsapi_key": AMAP_JSAPI_KEY if expose_js_keys else "",
            "security_js_code": AMAP_SECURITY_JS_CODE if expose_js_keys else "",
            "service_host": AMAP_SERVICE_HOST if expose_js_keys else "",
            "webservice_available": bool(AMAP_WEBSERVICE_KEY),
            "webservice_last_error": AMAP_LAST_ERROR.get("message", ""),
            "mcp_available": bool(AMAP_MCP_KEY),
            "jsapi_skill_available": os.path.exists(os.path.join(os.path.dirname(BASE_DIR), "amap-jsapi-skill", "SKILL.md")),
        },
        "baidu": {
            "browser_available": bool(BAIDU_BROWSER_AK) and expose_js_keys,
            "browser_ak": BAIDU_BROWSER_AK if expose_js_keys else "",
            "server_available": bool(BAIDU_AK),
        },
        "fallbacks": ["baidu", "google"],
    })


@app.route("/api/amap/geocode", methods=["GET", "OPTIONS"])
def api_amap_geocode():
    if request.method == "OPTIONS":
        return jsonify({"ok": True})
    address = request.args.get("address", "").strip()
    city = request.args.get("city", "").strip()
    if not address:
        return jsonify({"success": False, "error": "address不能为空"}), 400
    r = geocode_amap(address, city)
    if r:
        return jsonify({"success": True, "data_source": "amap", "tool_name": "amap-lbs-skill", "elapsed_ms": r.get("elapsed_ms", 0), "result": r})
    return jsonify({"success": False, "data_source": "amap", "tool_name": "amap-lbs-skill", "elapsed_ms": 0, "error": "高德地理编码不可用或未找到地址"}), 502


@app.route("/api/amap/search", methods=["GET", "POST", "OPTIONS"])
def api_amap_search():
    if request.method == "OPTIONS":
        return jsonify({"ok": True})
    b = request.get_json(silent=True) or {}
    query = (b.get("query") or request.args.get("query", "")).strip()
    city = (b.get("city") or request.args.get("city", "")).strip()
    location = (b.get("location") or request.args.get("location", "")).strip()
    limit = int(b.get("limit") or request.args.get("limit") or 10)
    if not query:
        return jsonify({"success": False, "error": "query不能为空"}), 400
    results = search_amap_place(query, city, limit, location)
    err_msg = "" if results else (AMAP_LAST_ERROR.get("message") or "高德POI无结果或未配置 AMAP_WEBSERVICE_KEY")
    return jsonify({
        "success": bool(results),
        "data_source": "amap",
        "tool_name": "amap-lbs-skill",
        "elapsed_ms": (results[0].get("elapsed_ms", 0) if results else 0),
        "provider": "gaode",
        "city": city,
        "query": query,
        "results": results,
        "count": len(results),
        "error": err_msg,
        "message": err_msg,
    })


@app.route("/api/amap/direction", methods=["POST", "OPTIONS"])
def api_amap_direction():
    if request.method == "OPTIONS":
        return jsonify({"ok": True})
    b = request.get_json(force=True)
    origin = b.get("origin", "")
    destination = b.get("destination", "")
    mode = b.get("mode", "walking")
    city = b.get("city", "")
    if not origin or not destination:
        return jsonify({"success": False, "error": "origin 和 destination 不能为空"}), 400
    r = route_amap(origin, destination, mode, city)
    return jsonify(r), (200 if r.get("success") else 502)


@app.route("/api/debug/tools", methods=["GET", "OPTIONS"])
def api_debug_tools():
    if request.method == "OPTIONS":
        return jsonify({"ok": True})
    return jsonify({
        "success": True,
        "tools": _debug_tool_chain(),
        "raw": _recent_tool_calls(),
    })


@app.route("/api/health", methods=["GET"])
def health():
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
        "ai":        _llm_status_text(),
        "rag":       f"米其林知识库 ({'✅' if MICHELIN_AVAILABLE else '⚠️知识库不可用，CSV兜底可用'})",
        "nearest":   "最近米其林 Haversine ✅",
        "meituan":   f"美团开放平台 ({'✅已配置 MEITUAN_API_KEY' if meituan_key else '⚠️未配置（需申请）'})",
        "meituan_skills": _meituan_skill_status(),
        "gaode":     f"高德地图优先（JSAPI {'✅' if AMAP_JSAPI_KEY else '⚠️'} / MCP {'✅' if AMAP_MCP_KEY else '⚠️'} / WebService {'✅' if AMAP_WEBSERVICE_KEY else '⚠️'}）",
        "meituan_tools": len(_MEITUAN_TOOLS),
        "route_profiles": ROUTE_PROFILES,
        "persona_profiles": PERSONA_PROFILES,
    })


if __name__ == "__main__":
    print("="*55)
    print("🍊 马到橙功后端 v3.8 启动")
    print(f"   DeepSeek : {'✅ 已配置' if DEEPSEEK_API_KEY else '❌ 请设置DEEPSEEK_API_KEY'}")
    print(f"   LongCat  : {'✅ 已配置' if LONGCAT_API_KEY else '⚠️  export LONGCAT_API_KEY=xxx'}")
    print(f"   米其林知识库: {'✅ 初始化中（后台加载）' if MICHELIN_AVAILABLE else '⚠️  知识库不可用，启用CSV兜底'}")
    print("   最近米其林: ✅ Haversine 地理索引")
    mt_count = len(_MEITUAN_TOOLS)
    print(f"   美团 Skill : {'✅ 已加载 '+str(mt_count)+'个工具' if mt_count else '⚠️  meituan_skill_tool.json 未找到'}")
    print("   多轮对话 : ✅ 最近12轮记忆")
    print(f"   Soul管家 : ✅ {_soul_memory_summary()}")
    print("   人格路线 : ✅ Agent自动推荐 + 用户可切换")
    print("   全景出行 : ✅ 跨国/跨省/跨城自动判定交通方式")
    print("   周末Agent: ✅ 真实路线优先 + 活动规划 + 三地图链接 + 智能兜底")
    print("   美团行程 : ✅ 规则路由 + 预算闭环 + 酒店/美食/景点并发匹配")
    mt_api_k = os.environ.get("MEITUAN_API_KEY","")
    print(
        "   高德地图  : "
        f"JSAPI {'✅ 已配置' if AMAP_JSAPI_KEY else '⚠️  export AMAP_JSAPI_KEY=xxx'} / "
        f"MCP {'✅ 已配置' if AMAP_MCP_KEY else '⚠️  export AMAP_MCP_KEY=xxx'} / "
        f"WebService {'✅ 已配置' if AMAP_WEBSERVICE_KEY else '⚠️  export AMAP_WEBSERVICE_KEY=xxx'}"
    )
    print(f"   美团API  : {'✅ 已配置' if mt_api_k else '⚠️  export MEITUAN_API_KEY=xxx（需申请）'}")
    print("="*55)
    app.run(
        host="0.0.0.0",
        port=5000,
        debug=False,
        threaded=True,
        use_reloader=False,
    )
