from flask import Flask, render_template, request, jsonify, session, redirect
from pymongo import MongoClient
from bson import ObjectId
from werkzeug.security import generate_password_hash, check_password_hash
import os
import json
import random
import re
import secrets
import time
import requests
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from dotenv import load_dotenv

load_dotenv()  # 같은 폴더의 .env 에서 TOURAPI_KEY / KAKAO_JS_KEY 로딩

app = Flask(__name__)
app.secret_key = os.environ.get("FLASK_SECRET_KEY") or secrets.token_hex(32)

# ============================================================
#  외부 API 설정
# ------------------------------------------------------------
#  TOURAPI_KEY : 공공데이터포털(data.go.kr)에서 발급받은
#                "한국관광공사_국문 관광정보 서비스_GW" 및
#                "한국관광공사_반려동물 동반여행 서비스" 인증키(Decoding).
#  KAKAO_JS_KEY: 카카오 개발자센터 JavaScript 키 (지도 표시용, 선택).
#
#  실제 배포 시 환경변수로 주입하세요.
#    export TOURAPI_KEY="발급받은_디코딩_키"
#    export KAKAO_JS_KEY="카카오_자바스크립트_키"
# ============================================================
TOURAPI_KEY  = os.environ.get("TOURAPI_KEY", "")
KAKAO_JS_KEY = os.environ.get("KAKAO_JS_KEY", "")
KAKAO_REST_KEY = os.environ.get("KAKAO_REST_KEY", "")

TOUR_BASE = "https://apis.data.go.kr/B551011"
KOR_SVC   = f"{TOUR_BASE}/KorService2"        # 국문 관광정보 (검색/공통/소개)
PET_SVC   = f"{TOUR_BASE}/KorPetTourService2" # 반려동물 동반여행 정보
GOCAMP    = f"{TOUR_BASE}/GoCamping"          # 고캠핑 정보 조회 (캠핑장 전용)

# 지역명 -> 관광공사 areaCode 매핑 (부분일치)
AREA_CODE = {
    "서울": 1, "인천": 2, "대전": 3, "대구": 4, "광주": 5, "부산": 6,
    "울산": 7, "세종": 8, "경기": 31, "강원": 32, "충북": 33, "충남": 34,
    "경북": 35, "경남": 36, "전북": 37, "전남": 38, "제주": 39,
}

# 고캠핑 doNm(도 이름) -> (표시용 short, areaCode) 매핑.
# 고캠핑은 '전라북도'/'전북특별자치도' 처럼 표기가 섞여 있어 별칭까지 담는다.
CAMP_DO_MAP = {
    "서울특별시": ("서울", 1), "서울시": ("서울", 1),
    "인천광역시": ("인천", 2),
    "대전광역시": ("대전", 3),
    "대구광역시": ("대구", 4),
    "광주광역시": ("광주", 5),
    "부산광역시": ("부산", 6),
    "울산광역시": ("울산", 7),
    "세종특별자치시": ("세종", 8), "세종시": ("세종", 8),
    "경기도": ("경기", 31),
    "강원도": ("강원", 32), "강원특별자치도": ("강원", 32),
    "충청북도": ("충북", 33),
    "충청남도": ("충남", 34),
    "경상북도": ("경북", 35),
    "경상남도": ("경남", 36),
    "전라북도": ("전북", 37), "전북특별자치도": ("전북", 37),
    "전라남도": ("전남", 38),
    "제주도": ("제주", 39), "제주특별자치도": ("제주", 39),
}


def map_doname(do_nm):
    """고캠핑 doNm -> (short, areaCode). 매핑 실패 시 (None, None)."""
    if not do_nm:
        return (None, None)
    do_nm = do_nm.strip()
    if do_nm in CAMP_DO_MAP:
        return CAMP_DO_MAP[do_nm]
    # 느슨한 폴백: 앞 2글자 기준 매칭 (예: '전라북도' -> '전라'로 시작하는 별칭)
    for full, pair in CAMP_DO_MAP.items():
        if full[:2] == do_nm[:2]:
            return pair
    return (None, None)


def short_from_text(text):
    """'제주', '경기 가평군' 같은 표시 텍스트 앞부분에서 AREA_CODE short 키를 찾는다."""
    if not text:
        return None
    head = text.split()[0]
    if head in AREA_CODE:
        return head
    for short in AREA_CODE:
        if head.startswith(short) or short in head:
            return short
    return None

# contentTypeId (TourAPI 4.0)
CT = {"tourist": 12, "culture": 14, "festival": 15, "leports": 28,
      "stay": 32, "shop": 38, "food": 39}

# areaCode -> 약칭 (역매핑)
SHORT_BY_CODE = {code: short for short, code in AREA_CODE.items()}

# 주소(addr1) 앞부분 -> areaCode 접두어 매칭 (긴 표기 먼저)
PROV_PREFIX = [
    ("서울", 1), ("인천", 2), ("대전", 3), ("대구", 4), ("광주", 5), ("부산", 6),
    ("울산", 7), ("세종", 8), ("경기", 31), ("강원", 32),
    ("충청북도", 33), ("충북", 33), ("충청남도", 34), ("충남", 34),
    ("경상북도", 35), ("경북", 35), ("경상남도", 36), ("경남", 36),
    ("전라북도", 37), ("전북", 37), ("전라남도", 38), ("전남", 38),
    ("제주", 39),
]


def addr_to_region(addr1):
    """반려동물 API의 addr1 주소 문자열을 (약칭, areaCode, 시군구명)으로 분해.
       areacode 필드가 대부분 비어 있어, 주소 텍스트로 직접 지역을 판별한다.
       매칭 실패 시 (None, None, None)."""
    if not addr1:
        return (None, None, None)
    toks = str(addr1).split()
    if not toks:
        return (None, None, None)
    head = toks[0]
    for pre, code in PROV_PREFIX:
        if head.startswith(pre):
            sig = toks[1] if len(toks) > 1 else None
            return (SHORT_BY_CODE.get(code), code, sig)
    return (None, None, None)


def _sig_key(s):
    """시군구명을 비교용 키로 정규화한다.
       공백 제거 + 뒤쪽 행정단위 접미사(특별시/광역시/시/군/구/도 등)를 '한 번만' 제거.
         예) '광진구'->'광진', '중구'->'중', '중랑구'->'중랑', '수원시'->'수원'
       이렇게 해야 '중구'(중)와 '중랑구'(중랑)가 서로 오매칭되지 않는다."""
    s = re.sub(r"\s+", "", (s or "").strip())
    s = re.sub(r"(특별자치시|특별자치도|특별시|광역시)$", "", s)
    s = re.sub(r"(시|군|구|도)$", "", s)
    return s


def sig_match(addr_sig, want):
    """주소에서 뽑은 시군구명(addr_sig)이 사용자가 고른 시군구(want)와 같은지.
       접미사를 정규화해 '정확히' 일치할 때만 True (부분 포함으로 인한 오매칭 방지)."""
    wk = _sig_key(want)
    if not wk:
        return True                       # 원하는 시군구가 없으면(=도 전체) 통과
    return _sig_key(addr_sig) == wk


def _addr_sig(addr):
    """전체 주소 문자열에서 시/군/구(둘째 토큰)만 뽑는다."""
    toks = str(addr or "").split()
    return toks[1] if len(toks) > 1 else ""


def address_matches_region(addr, prov_short=None, sigungu=None):
    """장소의 실제 주소(addr1/addr)를 선택 지역과 엄격하게 비교한다."""
    short, _code, addr_sig = addr_to_region(addr)
    if prov_short and short != prov_short:
        return False
    if sigungu and not sig_match(addr_sig, sigungu):
        return False
    return True

# 교통수단 -> 탐색 반경(m)
TRANSPORT_RADIUS = {
    "walk": 1500, "bicycle": 5000, "transit": 8000,
    "taxi": 10000, "car": 20000,
}

# MongoDB 연결
MONGO_URI = os.environ.get("MONGO_URI")

if not MONGO_URI:
    raise RuntimeError("MONGO_URI 환경변수가 설정되지 않았습니다.")

client = MongoClient(MONGO_URI, serverSelectionTimeoutMS=5000)
db = client["withgaegae"]


def get_current_user():
    if 'user_id' in session:
        return db.users.find_one({"user_id": session['user_id']})
    return None


@app.context_processor
def inject_globals():
    """모든 템플릿에서 카카오 키 사용 가능하도록 주입"""
    return {"KAKAO_JS_KEY": KAKAO_JS_KEY}


def resolve_area_code(text):
    if not text:
        return None
    for name, code in AREA_CODE.items():
        if name in text:
            return code
    return None


def tour_get(base, operation, params, items_key="item", timeout=8, retries=0):
    """
    TourAPI 공통 호출 래퍼.
    성공 시 item 리스트를 반환, 실패/빈결과 시 빈 리스트.
    실패 시 진단을 위해 http_status / error / raw(응답 앞부분)를 함께 담는다.

    timeout : 요청 타임아웃(초). 대량조회처럼 응답이 큰 호출은 늘려 잡는다.
    retries : 타임아웃/연결오류 시 재시도 횟수(기본 0 = 기존 동작 유지).
    """
    if not TOURAPI_KEY:
        # 키 미설정 시 프론트가 데모 모드로 동작하도록 신호
        return {"_no_key": True, "items": []}

    common = {
        "serviceKey": TOURAPI_KEY,
        "MobileOS": "ETC",
        "MobileApp": "withgaegae",
        "_type": "json",
    }
    common.update(params)

    r = None
    for attempt in range(retries + 1):
        try:
            r = requests.get(f"{base}/{operation}", params=common, timeout=timeout)
            r.raise_for_status()
            break
        except Exception as e:
            if attempt < retries:
                time.sleep(0.8 * (attempt + 1))   # 잠깐 쉬고 재시도(일시적 타임아웃 흡수)
                continue
            print(f"[TourAPI HTTP ERROR] {operation}: {e}")
            return {"_no_key": False, "items": [], "error": str(e)}

    # data.go.kr은 키 미신청/한도초과 시 200 상태로 XML 에러 본문을 주기도 한다.
    try:
        data = r.json()
    except Exception as e:
        snippet = (r.text or "")[:400]
        print(f"[TourAPI NON-JSON] {operation}: {e}\n  ↳ 응답앞부분: {snippet}")
        return {"_no_key": False, "items": [], "error": "NON_JSON_RESPONSE",
                "http_status": r.status_code, "raw": snippet}

    body = data.get("response", {}).get("body", {})
    header = data.get("response", {}).get("header", {})
    result_code = header.get("resultCode")
    # 정상 응답의 resultCode는 '0000'. 그 외는 에러(키/서비스 문제 등)
    if result_code not in (None, "0000", "00"):
        msg = header.get("resultMsg", "")
        print(f"[TourAPI RESULT ERROR] {operation}: {result_code} {msg}")
        return {"_no_key": False, "items": [], "error": f"{result_code} {msg}",
                "http_status": r.status_code}

    items = body.get("items", "")
    if not items or items == "":
        return {"_no_key": False, "items": [], "total": body.get("totalCount", 0)}
    item = items.get(items_key, [])
    # 단일 결과는 dict로 오므로 리스트로 정규화
    if isinstance(item, dict):
        item = [item]
    return {"_no_key": False, "items": item, "total": body.get("totalCount", len(item))}


def norm_place(it):
    """관광정보 item을 프론트 표준 형태로 정규화"""
    return {
        "contentid": it.get("contentid"),
        "contenttypeid": it.get("contenttypeid"),
        "title": it.get("title", "").strip(),
        "addr": (it.get("addr1", "") + " " + it.get("addr2", "")).strip(),
        "tel": it.get("tel", "") or "",
        "image": it.get("firstimage", "") or it.get("firstimage2", "") or "",
        "mapx": float(it["mapx"]) if it.get("mapx") else None,   # 경도(lng)
        "mapy": float(it["mapy"]) if it.get("mapy") else None,   # 위도(lat)
        "dist": round(float(it["dist"]) / 1000, 1) if it.get("dist") else None,  # km
        "cat": it.get("cat3", ""),
    }


def norm_camp(it, dog=None):
    """고캠핑 item을 프론트 표준 형태로 정규화하고 등록 반려견 기준으로 판정."""
    animal = (it.get("animalCmgCl") or "").strip()
    return {
        "title": (it.get("facltNm") or "").strip(),
        "addr": ((it.get("addr1") or "") + " " + (it.get("addr2") or "")).strip(),
        "tel": it.get("tel", "") or "",
        "mapx": float(it["mapX"]) if it.get("mapX") else None,   # 경도(lng)
        "mapy": float(it["mapY"]) if it.get("mapY") else None,   # 위도(lat)
        "animal": animal,                                        # 애완동물 동반 가능여부
        "verdict": camp_verdict(animal, dog),
        "intro": (it.get("lineIntro") or it.get("intro") or "").strip(),
        "facility": (it.get("sbrsCl") or "").replace(",", " · "),
        "induty": it.get("induty", ""),                          # 업종(일반/자동차/글램핑 등)
        "homepage": _clean_homepage(it.get("homepage", "")),
        "image": it.get("firstImageUrl", "") or "",
    }


def camp_verdict(animal, dog=None):
    """고캠핑 animalCmgCl을 등록 반려견 기준으로 판정.

    단순히 '가능(소형견)'을 조건부로 분류하지 않는다.
    사용자 반려견이 조건을 충족하면 동반 가능(ok),
    충족하지 않으면 동반 불가(no),
    반려견 정보가 없거나 자동 판정할 수 없는 조건이면 확인 필요(conditional)로 둔다.
    """
    import re

    if not animal:
        return "no_info"
    a = animal.replace(" ", "")
    if "불가" in a:
        return "no"
    if "가능" not in a:
        return "no_info"

    # 고캠핑의 '가능(소형견)', '가능(15kg미만)' 같은 조건도
    # 사용자 반려견 정보와 먼저 대조한다.
    kind, val = size_limit_from(a)
    if kind in ("kg", "kg_lt"):
        if dog and dog.get("weight") is not None:
            try:
                w = float(dog.get("weight"))
                over = (w >= val) if kind == "kg_lt" else (w > val)
                if over:
                    return "no"
            except (TypeError, ValueError):
                return "conditional"
        else:
            return "conditional"
    elif kind == "bucket":
        dog_size = dog_size_from(dog.get("weight"), dog.get("size")) if dog else None
        if dog_size:
            if SIZE_RANK[dog_size] > SIZE_RANK[val]:
                return "no"
        else:
            return "conditional"
    elif kind == "cm":
        return "conditional"

    # 조건을 충족했더라도 전화문의/사전협의/일부 구역 등의 문구가 있으면
    # '동반 가능 + 문의'로 남긴다.
    inquiry = any(k in a for k in (
        "전화문의", "문의요망", "사전협의", "협의필요", "개별문의",
        "사전문의", "사전확인", "문의필요", "문의필수", "일부구역", "일부시설",
        "실외좌석", "켄넬", "이동장"
    ))
    return "conditional" if inquiry else "ok"


def _clean_homepage(raw):
    """homepage 필드에 종종 섞인 <a href> 태그에서 URL만 추출"""
    if not raw:
        return ""
    import re
    m = re.search(r'href=["\']?([^"\'>\s]+)', raw)
    return m.group(1) if m else raw.strip()


def enrich_detail(places, limit=8):
    """추천 목록에 홈페이지/대표사진/간단소개를 detailCommon2로 채워 넣는다."""
    if not TOURAPI_KEY:
        return places
    for p in places[:limit]:
        cid = p.get("contentid")
        if not cid:
            continue
        res = tour_get(KOR_SVC, "detailCommon2", {
            "contentId": cid, "numOfRows": 1, "pageNo": 1,
        })
        items = res.get("items", [])
        if not items:
            continue
        d = items[0]
        hp = _clean_homepage(d.get("homepage", ""))
        if hp:
            p["homepage"] = hp
        if not p.get("image"):
            p["image"] = d.get("firstimage", "") or d.get("firstimage2", "") or ""
        ov = (d.get("overview") or "").strip()
        if ov:
            # 태그 제거 (길이 제한 없이 전체 표시)
            import re
            ov = re.sub(r"<[^>]+>", " ", ov)
            ov = re.sub(r"\s+", " ", ov).strip()
            p["overview"] = ov
        if not p.get("tel"):
            p["tel"] = d.get("tel", "") or ""
    return places


def fetch_pet_detail(content_id):
    """
    반려동물 동반 상세 정보 조회.
    반환: (has_pet_info: bool, detail: dict)
    """
    res = tour_get(PET_SVC, "detailPetTour2", {
        "contentId": content_id, "numOfRows": 1, "pageNo": 1,
    })
    items = res.get("items", [])
    if not items:
        return False, {}
    d = items[0]
    detail = {
        "accompany_type": d.get("acmpyTypeCd", ""),       # 동반유형
        "etc_info": d.get("etcAcmpyInfo", ""),            # 기타 동반정보
        "possible_pet": d.get("acmpyPsblCpam", ""),       # 동반 가능 반려동물
        "need_matter": d.get("acmpyNeedMtr", ""),         # 준비물
        "risk_matter": d.get("relaAcdntRiskMtr", ""),     # 사고 대비사항
        "rental": d.get("relaRntlPrdlst", ""),            # 렌탈 품목
        "furnish": d.get("relaFrnshPrdlst", ""),          # 비치 품목
        "facility": d.get("relaPosesFclty", ""),          # 관련 구비 시설
        "extra": d.get("relaPurcPrdlst", ""),             # 구매 품목
    }
    # 어떤 필드라도 값이 있으면 '동반 정보 있음'으로 판단
    has = any(v.strip() for v in detail.values() if isinstance(v, str))
    return has, detail


# =====================================================================
#  반려견 크기·타입 인지 판정 (Batch 2)
#   크기 기준: 소형 ~10kg / 중형 10~25kg / 대형 25kg+ / (특수) 맹인 안내견
# =====================================================================
SIZE_RANK = {"small": 1, "medium": 2, "large": 3}
SIZE_LABEL = {"small": "소형견", "medium": "중형견", "large": "대형견"}


def dog_size_from(weight, hint=None):
    """명시적 hint가 있으면 그걸, 없으면 무게(kg)로 크기 버킷 산출."""
    if hint in ("small", "medium", "large"):
        return hint
    try:
        w = float(str(weight).lower().replace("kg", "").strip())
    except (TypeError, ValueError):
        return None
    if w <= 10:
        return "small"
    if w <= 25:
        return "medium"
    return "large"


def representative_dog(dogs):
    """선택한 반려견들 중 '가장 제약이 큰' 기준견을 만든다.
       크기·무게는 가장 큰 값, 안내견은 전원이 안내견일 때만 True(보수적)."""
    if not dogs:
        return None
    sizes, guides, weights, danger = [], [], [], False
    for d in dogs:
        s = dog_size_from(d.get("weight"), d.get("size"))
        if s:
            sizes.append(s)
        guides.append(bool(d.get("guide")))
        try:
            weights.append(float(str(d.get("weight")).lower().replace("kg", "").strip()))
        except (TypeError, ValueError):
            pass
        if d.get("dangerous"):
            danger = True
    return {
        "size": max(sizes, key=lambda s: SIZE_RANK[s]) if sizes else None,
        "weight": max(weights) if weights else None,
        "guide": (all(guides) if guides else False),
        "dangerous": danger,
    }


def size_limit_from(text):
    """동반 가능 반려동물 문구에서 허용 한도 추정. 반환 (kind, val):
         ('all', None)   전 견종/모든/제한없음/…kg 이상 등 사실상 모두 허용
         ('kg', N)       N kg 이하·미만·이내
         ('bucket', 'small'|'medium'|'large')
         ('cm', None)    cm(길이/높이) 기준 → 무게로 환산 불가
         ('none', None)  크기 단서 없음"""
    import re
    t = (text or "").replace(" ", "")
    ALL_HINT = ("전견종", "전견동", "모든견", "모든반려", "견종무관", "크기무관",
                "제한없", "상관없", "반려동물동반", "애견동반", "개,고양이",
                "강아지,고양이", "반려견및반려묘")
    has_size_token = bool(re.search(r"\d+\s*(kg|cm)|소형|중형|대형", t, re.I))
    if any(k in t for k in ALL_HINT) and not has_size_token:
        return ("all", None)
    m = re.search(r"(\d+)\s*kg", t, re.I)
    if m:
        n = int(m.group(1))
        tail = t[m.end():m.end() + 3]
        if "이상" in tail or "초과" in tail:      # N kg 이상/초과 → 큰 개도 허용
            return ("all", None)
        if "미만" in tail:                        # N kg '미만' → 경계 불포함(엄격)
            return ("kg_lt", n)
        return ("kg", n)                          # N kg '이하/이내' → 경계 포함
    if re.search(r"\d+\s*cm", t, re.I):
        return ("cm", None)
    if "대형" in t:
        if re.search(r"대형.{0,10}(제외|불가|안됨|안돼|입실이불가|입장불가)", t):
            return ("bucket", "medium")          # 대형 제외 → 중형까지
        return ("bucket", "large")               # 대형 허용
    if any(k in t for k in ("중소형", "중,소형", "중·소형", "중/소형", "중형")):
        return ("bucket", "medium")
    if "소형" in t:
        return ("bucket", "small")
    return ("none", None)


def pet_verdict_for_dog(detail, dog):
    """상세 + 등록 반려견 -> 판정.  verdict: ok | check | no

    ── 판정 규칙(명확화) ─────────────────────────────────────────────
      · 불가(no)      : 안내견 전용인데 안내견이 아님 / 등록 반려견이 명시된
                        무게·크기 한도를 초과 / 동반가능동물 칸이 '불가'로 명시.
      · 가능(ok)      : ①동반 가능 반려동물(크기·견종)이 적혀 있고
                        ②등록 반려견이 그 조건을 충족하며
                        ③'전구역' 동반가능이고 ④문의·구역제한 신호가 없을 때만.
      · 확인 필요(check): 위 '가능' 4가지 중 하나라도 확정 불가할 때.
                        (대표: 동반가능동물 칸이 비어 크기를 알 수 없음 / 일부구역 /
                         이동장·문의 단서 / cm 기준 등)  → '무엇이 비었는지' 함께 안내.
    """
    import re

    def R_ok(msg):    return {"verdict": "ok",    "reason": msg, "inquiry": False}
    def R_no(msg):    return {"verdict": "no",    "reason": msg, "inquiry": False}
    def R_check(msg): return {"verdict": "check", "reason": msg, "inquiry": True}

    pp = (detail.get("possible_pet") or "")     # acmpyPsblCpam (동반 가능 반려동물)
    etc = (detail.get("etc_info") or "")        # etcAcmpyInfo
    acc = (detail.get("accompany_type") or "")  # acmpyTypeCd (전구역/일부구역)
    ppt = pp.replace(" ", "")
    ett = etc.replace(" ", "")
    partial = ("일부" in acc)
    zone_known = ("전구역" in acc) or ("일부" in acc)

    has_any = any((detail.get(k) or "").strip()
                  for k in ("possible_pet", "accompany_type", "etc_info",
                            "need_matter", "risk_matter"))
    if not has_any:
        return R_check("동반은 가능하지만 세부 조건이 등록돼 있지 않아 확인이 필요해요. "
                       "방문 전 전화 확인을 권장합니다.")

    NEG = ("불가", "불가능", "불허", "금지")
    ALLOW_HINT = ("소형", "중형", "대형", "전견종", "전견동", "모든", "kg",
                  "제외", "안내견", "가능", "반려동물동반", "개,고양이", "강아지", "애견")

    # 1) 안내견/보조견 전용
    guide_only = (("안내견" in ppt) or ("보조견" in ppt)) and not any(
        k in ppt for k in ("소형", "중형", "대형", "전견종", "전견동", "모든",
                           "kg", "반려동물동반", "개,고양이", "강아지", "애견"))
    if guide_only:
        if dog and dog.get("guide"):
            return R_ok("맹인 안내견 동반이 가능한 곳이에요.")
        return R_no("안내견(보조견)만 동반 가능해, 등록하신 반려견은 입장이 어려워요.")

    # 2) 동반가능동물 칸이 '불가'로 명시
    if any(k in ppt for k in NEG) and not any(k in ppt for k in ALLOW_HINT):
        return R_no("이 장소는 반려동물 동반이 불가한 곳이에요.")

    # 구역/문의/이동장 신호
    inquiry_sig = any(k in (ppt + ett) for k in
                      ("전화문의", "문의요망", "사전협의", "협의필요", "개별문의",
                       "사전문의", "사전확인", "문의필요", "문의필수", "정책상이",
                       "매장별", "브랜드매장별", "상이"))
    restrict_sig = any(k in ett for k in
                       ("동반불가", "입장불가", "실내동반불가", "제한될수",
                        "일부매장", "일부시설", "동반제한"))
    kennel = any(k in ppt for k in ("이동장", "켄넬", "실외좌석", "실외만", "야외만", "안고"))

    def finalize_ok(base):
        """'가능' 4조건을 만족해도 구역/문의/이동장 단서가 있으면 확인 필요로 낮춘다."""
        if inquiry_sig:
            return R_check(base + " 다만 일부 구역·매장은 정책이 달라 방문 전 확인이 필요해요.")
        if partial:
            return R_check(base + " 다만 일부 구역만 동반 가능하니 방문 전 확인을 권장해요.")
        if kennel:
            return R_check(base + " 다만 이동장(켄넬) 등 조건이 있어 방문 전 확인을 권장해요.")
        if restrict_sig:
            return R_check(base + " 다만 일부 시설은 동반이 제한될 수 있어 방문 전 확인을 권장해요.")
        return R_ok(base)

    kind, val = size_limit_from(pp)

    # 3) 크기 조건이 명시된 경우: 등록 반려견과 대조
    if kind in ("kg", "kg_lt"):
        strict = (kind == "kg_lt")                     # 미만 = 경계 불포함
        limit_txt = f"{val}kg 미만" if strict else f"{val}kg 이하"
        if dog and dog.get("weight") is not None:
            w = dog["weight"]
            over = (w >= val) if strict else (w > val)  # 미만이면 값과 같아도 초과 처리
            if over:
                return R_no(f"{limit_txt}만 동반 가능한 곳이라, {w:g}kg 반려견은 어려워요.")
            return finalize_ok(f"{limit_txt} 동반 가능 · 등록하신 {w:g}kg 반려견은 조건을 충족해요.")
        return R_check(f"{limit_txt}만 동반 가능한 곳이에요. 반려견 무게를 등록하면 정확히 판정해 드려요.")

    if kind == "bucket":
        if dog and dog.get("size"):
            if SIZE_RANK[dog["size"]] > SIZE_RANK[val]:
                return R_no(f"{SIZE_LABEL[val]}까지 동반 가능한 곳이라, {SIZE_LABEL[dog['size']]}은 어려울 수 있어요.")
            return finalize_ok(f"{SIZE_LABEL[val]}까지 동반 가능 · 등록하신 {SIZE_LABEL[dog['size']]} 기준으로 충족해요.")
        return R_check(f"{SIZE_LABEL[val]}까지 동반 가능한 곳이에요. 반려견 크기를 등록하면 정확히 판정해 드려요.")

    if kind == "cm":
        return R_check("크기 기준이 길이(cm)로 표기돼 있어 등록 정보로 자동 판정이 어려워요. 방문 전 확인을 권장합니다.")

    if kind == "all":
        return finalize_ok("전 견종 등 크기 제한 없이 동반 가능한 곳이에요.")

    # kind == none : 동반 가능 반려동물(크기·견종) 칸이 비어 있어 크기를 확정할 수 없음
    #   → '무엇이 비었는지' 정확히 안내(구역은 아는데 크기만 없으면 그렇게 표기)
    if zone_known:
        zonetext = "일부 구역만 동반 가능" if partial else "전구역 동반 가능"
        return R_check(f"동반 구역은 '{zonetext}'으로 확인되지만, 동반 가능한 크기·견종 조건이 "
                       f"명시돼 있지 않아 확인이 필요해요. 방문 전 전화 문의를 권장합니다.")
    return R_check("동반은 가능하나 동반 가능한 크기·견종 조건이 명시돼 있지 않아 확인이 필요해요. "
                   "방문 전 전화 문의를 권장합니다.")


def _enrich_one(p, dog):
    """추천 카드 1건에 공통 상세(홈페이지/사진/소개)와 반려견 기준 판정을 함께 부착.
       (ThreadPoolExecutor로 병렬 호출해 지연을 줄인다)"""
    import re
    cid = p.get("contentid")
    if cid:
        res = tour_get(KOR_SVC, "detailCommon2", {"contentId": cid, "numOfRows": 1, "pageNo": 1})
        items = res.get("items", [])
        if items:
            d = items[0]
            hp = _clean_homepage(d.get("homepage", ""))
            if hp:
                p["homepage"] = hp
            if not p.get("image"):
                p["image"] = d.get("firstimage", "") or d.get("firstimage2", "") or ""
            if not p.get("tel"):
                p["tel"] = d.get("tel", "") or ""
            ov = (d.get("overview") or "").strip()
            if ov:
                ov = re.sub(r"<[^>]+>", " ", ov)
                ov = re.sub(r"\s+", " ", ov).strip()
                p["overview"] = ov   # 설명 전체 표시(자르지 않음)
        has_pet, detail = fetch_pet_detail(cid)
    else:
        has_pet, detail = False, {}

    if has_pet:
        vd = pet_verdict_for_dog(detail, dog)
        p["detail"] = detail
        p["verdict"] = vd["verdict"]
        p["reason"] = vd["reason"]
        p["inquiry"] = vd["inquiry"]
    else:
        # 반려동물 동반 목록에 오른 곳은 전건(9,694곳) 동반 가능으로 확인됨.
        # 다만 상세조건이 등록된 곳은 999곳(10.3%)뿐이라, 나머지는 '가능·문의 권장'으로 안내한다.
        p["detail"] = {}
        p["verdict"] = "check"
        p["reason"] = ("이곳은 반려동물 동반이 가능한 곳이에요. 다만 무게·구역 등 세부 조건이 "
                       "공식 데이터에 등록되어 있지 않아, 방문 전 전화로 확인하시길 권장해요.")
        p["inquiry"] = True
    return p


def verified_alternatives(pet_items, prov_short, sigungu_name, dog, limit=6):
    """장소 검색 실패 시 보여줄 대체 장소도 동일한 반려견 판정 로직을 적용한다.

    대체 장소는 이미 한국관광공사 반려동물 동반여행 API 목록에서 가져오므로
    _enrich_one()으로 상세 API + 등록 반려견 조건을 다시 판정한 뒤,
    둘러보기와 동일하게 ok/check만 반환한다.
    """
    if not pet_items:
        return []

    candidates = pets_in_region(prov_short, sigungu_name, limit=max(limit * 4, 20))
    candidates = [x for x in candidates if is_recommendable_place(x)]
    if not candidates:
        return []

    with ThreadPoolExecutor(max_workers=8) as ex:
        enriched = list(ex.map(lambda x: _enrich_one(x, dog), candidates))

    return [x for x in enriched if x.get("verdict") in ("ok", "check")][:limit]


# =====================================================================
#  페이지 뷰 라우팅
# =====================================================================

@app.route('/')
def main_page():
    user = get_current_user()
    home_trips = []
    home_ongoing = None
    home_planned = []
    if user:
        home_trips = list(db.travel.find({"user_id": user["user_id"]}).sort("created", -1).limit(6))
        for t in home_trips:
            t["_id"] = str(t["_id"])
            t["status"] = effective_status(t)
        home_ongoing = next((t for t in home_trips if t["status"] == "ongoing"), None)
        home_planned = [t for t in home_trips if t["status"] == "planned"]
    return render_template(
        'main.html',
        user=user,
        home_ongoing=home_ongoing,
        home_planned=home_planned,
        home_trips=home_trips,
    )

def effective_status(trip, today=None):
    """여행의 실제 표시 상태를 계산한다.

    - 확정된 여행 + 오늘이 여행 기간 안: 진행 중
    - 확정된 여행 + 여행 기간이 지난 경우: 다녀옴
    - 확정된 여행 + 아직 시작 전: 계획 중
    - 미확정 자동저장 여행: 날짜와 관계없이 계획 중

    confirmed가 True인 여행만 실제 여행 상태(진행 중/다녀옴)로 계산한다.
    confirmed가 없거나 False이면 날짜와 관계없이 계획 중으로 둔다.
    """
    today = today or datetime.now().strftime("%Y-%m-%d")
    if trip.get("done_override"):
        return "done"

    # 확정 버튼을 누른 여행만 날짜에 따라 진행 중/다녀옴으로 전환한다.
    # confirmed 필드가 없는 예전 데이터는 새 기준에서 '확정 전'으로 취급한다.
    confirmed = bool(trip.get("confirmed", False))
    if not confirmed:
        return "planned"

    start = trip.get("start") or ""
    end = trip.get("end") or ""

    if end and today > end:
        return "done"
    if start and today < start:
        return "planned"
    if start and end and start <= today <= end:
        return "ongoing"
    if start and not end and today >= start:
        return "ongoing"
    return "planned"


@app.route('/mypage')
def mypage():
    user = get_current_user()
    if not user:
        return render_template('main.html', user=None)
    travels = list(db.travel.find({"user_id": user["user_id"]}).sort("created", -1))
    for t in travels:
        t["_id"] = str(t["_id"])
        t["status"] = effective_status(t)   # 날짜 기준 실시간 상태

    ongoing = next((t for t in travels if t["status"] == "ongoing"), None)
    planned = [t for t in travels if t["status"] == "planned"]
    records = [t for t in travels if t["status"] == "done"]

    # 반려견: 원본 배열 인덱스(_i)를 함께 넘겨 수정/삭제 시 정확히 지정
    dogs = []
    for i, d in enumerate(user.get("dogs", [])):
        if (d.get("name") or "").strip():
            d2 = dict(d)
            d2["_i"] = i
            dogs.append(d2)
    photo_by_name = {d.get("name"): d.get("photo", "") for d in user.get("dogs", [])}

    # 지도: 완료된 여행의 '장소'만 마커로 표시한다.
    # 마커를 누르면 여행 이름/날짜/동행 반려견/일차를 보여줄 수 있도록
    # 여행 정보를 함께 넘긴다. 반려견 사진은 지도 마커에 사용하지 않는다.
    map_stops = []
    for t in travels:
        if t["status"] != "done":
            continue
        for s in t.get("stops", []):
            if s.get("lat") and s.get("lng"):
                map_stops.append({
                    "name": s.get("name"),
                    "addr": s.get("addr", ""),
                    "lat": s.get("lat"),
                    "lng": s.get("lng"),
                    "trip_id": t.get("_id"),
                    "trip": t.get("title", "여행"),
                    "start": t.get("start", ""),
                    "end": t.get("end", ""),
                    "dogs": t.get("dogs", []),
                    "day": s.get("day"),
                })

    # 이용 기록: 어떤 '장소'를 담았는지 (여행 단위가 아니라 장소 단위)
    place_log = []
    for t in travels:   # created 최신순
        for s in t.get("stops", []):
            place_log.append({"name": s.get("name"), "trip": t.get("title"),
                              "date": t.get("start"), "verdict": s.get("verdict", "")})

    return render_template('mypage.html', user=user, dogs=dogs,
                           ongoing=ongoing, planned=planned, records=records,
                           all_trips=travels, place_log=place_log, map_stops=map_stops)

@app.route('/travel')
def travel_page():
    user = get_current_user()
    if not user:
        return redirect('/')   # 로그인해야 여행 시작 가능

    edit_trip = None
    trip_id = request.args.get('trip_id')
    if trip_id:
        try:
            edit_trip = db.travel.find_one({"_id": ObjectId(trip_id), "user_id": user["user_id"]})
            if edit_trip:
                # 예전에 저장한 여행에 지역 코드가 없더라도 첫 장소 주소로 복원한다.
                if not edit_trip.get("region") and edit_trip.get("stops"):
                    first_addr = (edit_trip.get("stops") or [{}])[0].get("addr", "")
                    sh, code, sig = addr_to_region(first_addr)
                    if sh:
                        edit_trip["region"] = sh + (f" {sig}" if sig else "")
                        edit_trip["region_do"] = sh
                        edit_trip["area_code"] = code
                        edit_trip["sigungu_name"] = sig
                edit_trip["_id"] = str(edit_trip["_id"])
        except Exception:
            edit_trip = None

    return render_template('travel.html', user=user, edit_trip=edit_trip)

@app.route('/result')
def result_page():
    # [레거시] 예전 결과 화면. 실데이터 판정/추천은 모두 /travel 플로우로 통합되었고
    # 이 화면은 어디에서도 링크되지 않으며 정적 데모(db.places)만 보여주던 화면이라
    # 홈으로 보낸다. (템플릿/엔드포인트 자체는 남겨 두어 삭제로 인한 오류를 방지)
    return redirect('/')


# =====================================================================
#  관광 API 프록시 (인증키를 서버에 숨기고 CORS 우회)
# =====================================================================

KAKAO_LOCAL_URL = "https://dapi.kakao.com/v2/local/search/keyword.json"

# 검증/대체추천에서 실제 여행지로 취급할 콘텐츠 유형.
# 병원·약국·은행·편의점·주유소 등 생활시설은 추천에서 제외한다.
RECOMMENDABLE_CONTENT_TYPES = {"12", "14", "15", "28", "32", "39"}
IRRELEVANT_PLACE_WORDS = (
    "약국", "병원", "의원", "한의원", "보건소", "은행", "편의점", "주유소",
    "충전소", "세차", "자동차정비", "정비소", "부동산", "학원", "학교",
    "어린이집", "유치원", "주민센터", "행정복지센터", "우체국", "장례",
    "요양원", "요양병원", "세탁소", "미용실", "이발소", "노래방",
)


def is_recommendable_place(place):
    """여행지 대체추천 카드에 넣어도 되는지 1차 필터."""
    ct = str(place.get("contenttypeid") or "")
    if ct and ct not in RECOMMENDABLE_CONTENT_TYPES:
        return False
    text = f"{place.get('title', '')} {place.get('addr', '')}".replace(" ", "")
    return not any(word.replace(" ", "") in text for word in IRRELEVANT_PLACE_WORDS)


def kakao_place_search(query, region=None, size=15, page=1):
    """카카오 Local 키워드 검색.

    장소 검증에서는 한 번의 검색 결과만 믿지 않고 페이지를 넘겨가며 찾는다.
    Kakao Local 키워드 검색은 페이지당 최대 15건, 최대 45페이지를 제공한다.
    """
    if not KAKAO_REST_KEY:
        return [], "NO_KEY"

    params = {
        "query": query,
        "size": min(max(int(size), 1), 15),
        "page": min(max(int(page), 1), 45),
    }
    headers = {"Authorization": f"KakaoAK {KAKAO_REST_KEY}"}
    try:
        r = requests.get(KAKAO_LOCAL_URL, params=params, headers=headers, timeout=6)
        r.raise_for_status()
        body = r.json()
        return body.get("documents", []) or [], None
    except Exception as e:
        print(f"[Kakao Local ERROR] {query} (page={page}): {e}")
        return [], str(e)


def norm_kakao_place(it):
    """Kakao Local 결과를 기존 장소 카드 형태로 변환."""
    x = it.get("x") or None
    y = it.get("y") or None
    try:
        x = float(x) if x is not None else None
        y = float(y) if y is not None else None
    except (TypeError, ValueError):
        x, y = None, None
    addr = (it.get("road_address_name") or it.get("address_name") or "").strip()
    return {
        "title": (it.get("place_name") or "").strip(),
        "addr": addr,
        "tel": (it.get("phone") or "").strip(),
        "mapx": x,
        "mapy": y,
        "place_url": (it.get("place_url") or "").strip(),
        "category_name": (it.get("category_name") or "").strip(),
        "category_group_code": (it.get("category_group_code") or "").strip(),
        "image": "",
    }


def _name_key(v):
    return re.sub(r"[^0-9a-zA-Z가-힣]", "", str(v or "")).lower()


def _address_key(v):
    return re.sub(r"\s+", "", str(v or "")).lower()


def match_kakao_to_pet(kakao, pet_items, prov_short=None, sigungu_name=None):
    """카카오 장소와 반려동물 API 장소를 이름+주소로 매칭.
    매칭 실패는 '동반 불가'가 아니라 '정보 확인 필요'로 처리한다.
    """
    from difflib import SequenceMatcher
    kt = _name_key(kakao.get("title"))
    ka = _address_key(kakao.get("addr"))
    best, best_score = None, 0.0
    for pet in pet_items:
        short, _code, addr_sig = addr_to_region(pet.get("addr1"))
        if prov_short and short != prov_short:
            continue
        if sigungu_name and not sig_match(addr_sig, sigungu_name):
            continue
        pt = _name_key(pet.get("title"))
        if not kt or not pt:
            continue
        if kt == pt:
            score = 1.0
        elif kt in pt or pt in kt:
            score = 0.93
        else:
            score = SequenceMatcher(None, kt, pt).ratio()
        pa = _address_key((pet.get("addr1") or "") + " " + (pet.get("addr2") or ""))
        if ka and pa:
            if ka == pa:
                score += 0.08
            elif ka[:8] and ka[:8] in pa:
                score += 0.04
        if score > best_score:
            best, best_score = pet, score
    return best if best_score >= 0.82 else None


def kakao_verify_candidates(name, prov_short=None, sigungu_name=None):
    """사용자가 입력한 장소명을 Kakao에서 찾고 선택지역 밖 결과를 제거한다.

    - 지역+장소명 검색을 우선한다.
    - 첫 페이지에서 끝내지 않고 최대 3페이지까지 확인한다.
    - 짧은 장소명은 '대학교', '대' 같은 자연스러운 검색어도 보조로 사용한다.
    - Kakao는 장소 식별만 담당하고, 반려동물 동반 여부는 이후 TourAPI에서 판정한다.
    """
    base = (name or "").strip()
    if not base:
        return [], []

    queries = []
    if sigungu_name:
        queries.append(f"{sigungu_name} {base}")
    elif prov_short:
        queries.append(f"{prov_short} {base}")
    queries.append(base)

    # '세종' → '세종대학교'처럼 사용자가 짧게 입력한 경우의 검색 보조.
    # 지나치게 긴 검색어는 임의 확장을 하지 않는다.
    if len(_name_key(base)) <= 4:
        queries.append(f"{base}대학교")
        queries.append(f"{base}대")

    # 중복 제거(순서 유지)
    queries = list(dict.fromkeys(q for q in queries if q.strip()))

    found, seen = [], set()
    errors = []
    for q in queries:
        for page in range(1, 4):
            docs, err = kakao_place_search(q, size=15, page=page)
            if err:
                errors.append(err)
                break

            for d in docs:
                p = norm_kakao_place(d)
                key = (_name_key(p["title"]), _address_key(p["addr"]))
                if key in seen:
                    continue

                # 선택한 지역 밖의 장소는 검증 대상에서 제외한다.
                if prov_short or sigungu_name:
                    raw_addresses = [
                        p.get("addr", ""),
                        d.get("address_name") or "",
                        d.get("road_address_name") or "",
                    ]
                    if not any(address_matches_region(a, prov_short, sigungu_name)
                               for a in raw_addresses if a):
                        continue

                seen.add(key)
                p["kakao"] = True
                p["_query"] = q
                found.append(p)

            # 현재 검색어의 다음 페이지가 없으면 다음 검색어로 이동한다.
            if len(docs) < 15:
                break

        # 충분한 지역 내 후보를 확보했으면 보조 검색어는 더 호출하지 않는다.
        if len(found) >= 10:
            break

    # 입력어와 이름이 직접 관련된 장소를 먼저 보여준다.
    target = _name_key(base)
    from difflib import SequenceMatcher

    def score(p):
        title = _name_key(p.get("title"))
        if title == target:
            name_score = 0
        elif target and target in title:
            name_score = 1
        elif title and title in target:
            name_score = 2
        else:
            name_score = 3
        similarity = SequenceMatcher(None, target, title).ratio() if target and title else 0
        return (name_score, -similarity)

    found.sort(key=score)
    return found[:10], errors[:3]


@app.route('/api/tour/verify', methods=['POST'])
def tour_verify():
    """입력 장소를 Kakao Local에서 먼저 찾고, 반려동물 동반여행 API와 교차 확인한다.

    상태 의미:
      - pet API에 등록 + 세부조건 충족: 동반 가능/확인 필요
      - pet API에 등록 + 세부조건상 불가: 동반 불가
      - Kakao에는 있지만 pet API에 없음: 동반 불가
      - Kakao에도 없음: 입력한 장소를 찾지 못함

    동반 가능 여부의 최종 기준은 한국관광공사 반려동물 동반여행 API이다.
    """
    data = request.json or {}
    name = (data.get("name") or "").strip()
    region = (data.get("region") or "").strip()
    parts = region.split()
    sigungu_name = (data.get("sigungu_name") or (parts[1] if len(parts) > 1 else None))
    dog = representative_dog(data.get("dogs"))
    try:
        area_code = int(data.get("area_code")) if data.get("area_code") else None
    except (TypeError, ValueError):
        area_code = None
    prov_short = SHORT_BY_CODE.get(area_code) or short_from_text(region)

    if not name:
        return jsonify({"success": False, "message": "장소명을 입력해주세요."}), 400
    if not TOURAPI_KEY:
        return jsonify({"success": False, "no_key": True,
                        "message": "TOURAPI_KEY 미설정 (데모 데이터로 표시)"})

    pet_items = load_all_pets()
    pet_error = _pet_cache.get("error")
    kakao_places, kakao_errors = kakao_verify_candidates(name, prov_short, sigungu_name)

    # Kakao REST 키가 아직 없으면 기존 TourAPI 검색을 유지하되,
    # 반려동물 API에 등록되지 않은 장소는 이 서비스 기준으로 동반 불가 처리한다.
    if not KAKAO_REST_KEY:
        variants = [name]
        if " " in name:
            variants += [name.replace(" ", ""), max(name.split(), key=len)]
        kor_hits, kor_err = [], False
        seen = set()
        for kw in variants:
            for page in range(1, 4):
                res = tour_get(KOR_SVC, "searchKeyword2", {
                    "keyword": kw, "numOfRows": 100, "pageNo": page, "arrange": "O",
                    **({"areaCode": area_code} if area_code else {})
                })
                if res.get("error"):
                    kor_err = True
                    break
                for it in res.get("items", []):
                    cid = it.get("contentid")
                    if not cid or cid in seen:
                        continue
                    if region and not address_matches_region(
                            it.get("addr1", ""), prov_short, sigungu_name):
                        continue
                    seen.add(cid)
                    kor_hits.append(it)
                if len(res.get("items", [])) < 100:
                    break
            if kor_hits:
                break
        candidates = [norm_place(it) for it in kor_hits[:30]]
        for p in candidates:
            pet = match_kakao_to_pet(p, pet_items, prov_short, sigungu_name)
            p["pet_registered"] = bool(pet)
            if pet:
                if not p.get("addr"):
                    p["addr"] = ((pet.get("addr1") or "") + " " + (pet.get("addr2") or "")).strip()
                _enrich_one(p, dog)
            else:
                p["verdict"] = "no"
                p["reason"] = "한국관광공사 반려동물 동반여행 API에 등록된 장소가 아니어서 동반 불가로 안내합니다."
                p["inquiry"] = False
        if not candidates:
            alts = verified_alternatives(pet_items, prov_short, sigungu_name, dog, limit=6)
            return jsonify({"success": True, "results": [], "query": name,
                            "alternatives": alts, "message": "입력한 장소를 찾지 못했어요.",
                            "kakao_available": False})
        return jsonify({"success": True, "results": candidates,
                        "query": name, "alternatives": [],
                        "kakao_available": False, "kor_search_error": kor_err})

    if not kakao_places:
        alts = verified_alternatives(pet_items, prov_short, sigungu_name, dog, limit=6)
        message = "입력한 장소를 찾지 못했어요. 장소명을 확인해 주세요."
        if pet_error:
            message += " 반려동물 동반 데이터 조회에도 문제가 있어요."
        return jsonify({"success": True, "results": [], "query": name,
                        "alternatives": alts, "message": message,
                        "kakao_available": True, "kakao_errors": kakao_errors[:2]})

    results = []
    for kp in kakao_places:
        p = dict(kp)
        pet = match_kakao_to_pet(kp, pet_items, prov_short, sigungu_name)
        p["pet_registered"] = bool(pet)
        if pet:
            p["contentid"] = pet.get("contentid")
            p["contenttypeid"] = pet.get("contenttypeid")
            if not p.get("addr"):
                p["addr"] = ((pet.get("addr1") or "") + " " + (pet.get("addr2") or "")).strip()
            if not p.get("image"):
                p["image"] = pet.get("firstimage", "") or pet.get("firstimage2", "") or ""
            _enrich_one(p, dog)
            if p.get("verdict") == "no":
                # 상세 데이터에 명시적인 제한이 있는 경우만 실제 '동반 불가'.
                p["reason"] = p.get("reason") or "등록하신 반려견 기준 동반이 어려운 조건이 확인됐어요."
        else:
            p["verdict"] = "no"
            p["reason"] = "한국관광공사 반려동물 동반여행 API에 등록된 장소가 아니어서 동반 불가로 안내합니다."
            p["inquiry"] = False
        results.append(p)

    target = _name_key(name)
    results.sort(key=lambda p: (
        0 if _name_key(p.get("title")) == target else
        1 if target and target in _name_key(p.get("title")) else 2,
        {"ok": 0, "check": 1, "conditional": 1, "no": 2}.get(p.get("verdict"), 3)
    ))
    return jsonify({"success": True, "results": results[:10], "query": name,
                    "alternatives": [], "kakao_available": True})


def recommend_nearby(mapx=None, mapy=None, area_code=None, sigungu_code=None,
                     radius=8000, content_type=None, limit=6):
    """반려동물 동반 가능한 주변/지역 장소 추천 (PET_SVC 직접 조회)."""
    if mapx and mapy:
        params = {"mapX": mapx, "mapY": mapy, "radius": radius,
                  "numOfRows": limit, "pageNo": 1, "arrange": "E"}
        if content_type:
            params["contentTypeId"] = content_type
        res = tour_get(PET_SVC, "locationBasedList2", params)
    elif area_code:
        params = {"areaCode": area_code, "numOfRows": limit, "pageNo": 1,
                  "arrange": "O"}
        if sigungu_code:
            params["sigunguCode"] = sigungu_code
        if content_type:
            params["contentTypeId"] = content_type
        res = tour_get(PET_SVC, "areaBasedList2", params)
    else:
        return []
    return [norm_place(it) for it in res.get("items", [])]


@app.route('/api/tour/recommend', methods=['POST'])
def tour_recommend():
    """
    [추천] 반려동물 동반 가능한 숙소/식당/카페/축제/캠핑 추천.
    body: { area_code, city, kind, transport, mapx, mapy }
      kind: stay | food | festival | tourist | camping
    """
    data = request.json or {}
    kind = data.get("kind", "stay")
    transport = data.get("transport", "car")
    mapx = data.get("mapx")
    mapy = data.get("mapy")
    region = (data.get("region") or "").strip()   # 예: "경기 수원시" (주소 필터용)
    sigungu_code = data.get("sigungu_code") or None
    dog = representative_dog(data.get("dogs"))
    try:
        area_code = int(data.get("area_code")) if data.get("area_code") else None
    except (TypeError, ValueError):
        area_code = None

    radius = TRANSPORT_RADIUS.get(transport, 20000)
    content_type = CT.get("stay" if kind == "camping" else kind)

    if not TOURAPI_KEY:
        return jsonify({"success": True, "no_key": True, "places": []})

    if mapx and mapy:
        # 좌표가 있으면 반경 기반(교통수단 반영)
        places = recommend_nearby(mapx=mapx, mapy=mapy, radius=radius,
                                  content_type=content_type, limit=30)
    else:
        # 좌표가 없으면 '주소'로 분류한 전량 풀에서 지역 필터 (areacode 미비 우회 → 데이터 풍부)
        prov_short = SHORT_BY_CODE.get(area_code) or short_from_text(region)
        parts = region.split()
        sigungu = data.get("sigungu_name") or (parts[1] if len(parts) > 1 else None)
        # 시군구를 고르면 그 시군구 안에서만 조회한다. 결과가 없다고 도 전체로 넓히지 않는다.
        places = pets_in_region(prov_short, sigungu, content_type, limit=40) if prov_short else []

    # 좌표 기반 조회를 사용한 경우에도 선택 지역을 실제 주소로 최종 검증한다.
    if region:
        parts = region.split()
        prov_short = SHORT_BY_CODE.get(area_code) or short_from_text(region)
        sigungu = data.get("sigungu_name") or (parts[1] if len(parts) > 1 else None)
        places = [p for p in places if address_matches_region(p.get("addr", ""), prov_short, sigungu)]

    if kind == "camping":
        kw = ("캠핑", "야영", "오토캠", "글램핑", "카라반")
        places = [p for p in places if any(k in p["title"] for k in kw)] or places

    places = [p for p in places if is_recommendable_place(p)]
    # 먼저 충분한 후보를 판정한 뒤 ok/check를 골라낸다.
    # 처음 15개가 반려견 조건과 맞지 않는다고 전체가 0개가 되는 것을 막는다.
    places = places[:40]
    # 각 카드에 공통 상세 + 반려견 기준 판정을 병렬로 부착
    with ThreadPoolExecutor(max_workers=8) as ex:
        places = list(ex.map(lambda p: _enrich_one(p, dog), places))
    # 판정이 좋은 순으로 정렬 (동반 불가는 맨 뒤)
    rank = {"ok": 0, "check": 1, "no_info": 1, "no": 2}
    places.sort(key=lambda p: rank.get(p.get("verdict"), 1))
    # 둘러보기/추천은 반드시 반려동물 API 기준으로 동반 가능 장소만 노출한다.
    # ok = 동반 가능, check = 동반 가능하지만 세부조건 확인 필요.
    places = [p for p in places if p.get("verdict") in ("ok", "check")]
    places = places[:15]

    return jsonify({"success": True, "no_key": False, "places": places,
                    "radius": radius, "kind": kind})


@app.route('/api/tour/locate', methods=['POST'])
def tour_locate():
    """장소명 -> 좌표/주소 확정 (호텔만 정함 플로우에서 사용)."""
    data = request.json or {}
    name = (data.get("name") or "").strip()
    try:
        area_code = int(data.get("area_code")) if data.get("area_code") else None
    except (TypeError, ValueError):
        area_code = None
    if not name:
        return jsonify({"success": False, "message": "장소명을 입력해주세요."}), 400
    params = {"keyword": name, "numOfRows": 1, "pageNo": 1}
    if area_code:
        params["areaCode"] = area_code
    res = tour_get(KOR_SVC, "searchKeyword2", params)
    if res.get("_no_key"):
        return jsonify({"success": True, "no_key": True, "place": None})
    hits = res.get("items", [])
    if not hits:
        return jsonify({"success": True, "found": False, "place": None})
    return jsonify({"success": True, "found": True, "place": norm_place(hits[0])})


# =====================================================================
#  지역 목록 (반려동물 동반 장소가 있는 지역만)
# =====================================================================
_region_cache = {"provinces": None, "sigungu": {}, "camp": None}

# 고캠핑 전체 캠핑장 캐시 (지역 인덱스 · 지역별 조회에 함께 사용)
_camp_cache = {"all": None, "error": None, "raw": None, "fetched": 0, "pet_ok": 0}

# 반려동물 동반여행 전체 목록 캐시 (전건 = 동반 가능).
# areacode 필드가 대부분 비어 있어(6%뿐), 목록을 전량 받아 '주소'로 지역을 나눈다.
_pet_cache = {"all": None, "index": None, "error": None, "fetched": 0, "complete": False}

# 반려동물 전량을 디스크에 저장해 두는 파일.
# data.go.kr 대량조회가 자주 끊기므로, 한 번 완전히 받으면 파일로 저장해서
# 이후엔 네트워크 없이 이 파일을 즉시 사용한다(공공API 장애/지연에 영향받지 않음).
PET_CACHE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "pets_cache.json")


def _read_pet_cache_file():
    """디스크에 저장된 반려동물 전량 캐시를 읽는다. 없거나 손상되면 None."""
    try:
        with open(PET_CACHE_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, list) and data:
            return data
    except Exception:
        pass
    return None


def _write_pet_cache_file(items):
    """반려동물 전량을 디스크에 저장(다음 실행부터 네트워크 없이 사용)."""
    try:
        with open(PET_CACHE_FILE, "w", encoding="utf-8") as f:
            json.dump(items, f, ensure_ascii=False)
        print(f"[pets_cache] 저장 완료: {len(items)}건 → {PET_CACHE_FILE}")
    except Exception as e:
        print(f"[pets_cache] 저장 실패: {e}")


def load_all_pets():
    """반려동물 동반여행 areaBasedList2 전량을 받아 캐시한다.
       (전국 약 9,694건 · 전건 동반 가능)

       순서:
       1) 메모리에 완전한 캐시가 있으면 그대로 사용.
       2) 디스크 캐시 파일(pets_cache.json)이 있으면 그것을 사용 → 네트워크 불필요.
       3) 둘 다 없으면 API로 조회(작은 페이지 500단위 + 재시도). 완전히 받으면
          디스크에 저장해 다음부턴 네트워크 없이 쓰도록 한다.

       (수정) 예전에는 중간 페이지가 타임아웃으로 끊겨도 그 '부분 결과'를 영구 캐시해서,
       네트워크가 회복돼도 계속 일부(예: 1000건)만 사용했다. 이제는 완전히 받았을 때만
       확정 캐시/파일저장하고, 끊기면 다음 호출에서 다시 시도해 스스로 회복한다."""
    if _pet_cache["all"] is not None and _pet_cache.get("complete"):
        return _pet_cache["all"]

    # (2) 디스크 캐시 우선
    disk = _read_pet_cache_file()
    if disk is not None:
        _pet_cache["all"] = disk
        _pet_cache["fetched"] = len(disk)
        _pet_cache["complete"] = True
        _pet_cache["index"] = None
        _pet_cache["error"] = None
        print(f"[pets_cache] 디스크 캐시 사용: {len(disk)}건")
        return disk

    if not TOURAPI_KEY:
        _pet_cache["all"] = []
        _pet_cache["error"] = "NO_KEY"
        _pet_cache["complete"] = True
        return []

    # (3) API 대량조회 — 페이지 500단위로 잘게, 넉넉한 타임아웃 + 재시도
    all_items, page, seen = [], 1, set()
    complete = True
    _pet_cache["error"] = None
    while page <= 40:
        res = tour_get(PET_SVC, "areaBasedList2",
                       {"numOfRows": 500, "pageNo": page, "arrange": "A"},
                       timeout=20, retries=2)
        if res.get("error"):
            _pet_cache["error"] = res.get("error")
            complete = False          # 중간에 끊김 → 부분 결과를 확정 캐시하지 않음
            break
        items = res.get("items", [])
        if not items:
            break
        for it in items:
            cid = it.get("contentid")
            if cid and cid not in seen:
                seen.add(cid)
                all_items.append(it)
        if len(items) < 500:
            break
        page += 1
    _pet_cache["all"] = all_items
    _pet_cache["fetched"] = len(all_items)
    _pet_cache["complete"] = complete
    _pet_cache["index"] = None        # 목록이 갱신됐으니 지역 인덱스도 재생성
    if complete and all_items:
        _write_pet_cache_file(all_items)   # 다음 실행부터 네트워크 없이 이 파일 사용
    return all_items


def build_pet_region_index():
    """반려동물 전량을 '주소'로 분류해 시/도·시/군/구별 개수 인덱스를 만든다."""
    if _pet_cache["index"] is not None:
        return _pet_cache["index"]
    prov_count = Counter()
    prov_code = {}
    sig_count = {}   # short -> Counter(시군구명)
    for it in load_all_pets():
        short, code, sig = addr_to_region(it.get("addr1"))
        if not short:
            continue
        prov_count[short] += 1
        prov_code[short] = code
        if sig:
            sig_count.setdefault(short, Counter())[sig] += 1

    provinces = [{"name": s, "code": prov_code[s], "count": n}
                 for s, n in prov_count.items()]
    provinces.sort(key=lambda p: p["count"], reverse=True)

    sigungu = {}
    for s, cnt in sig_count.items():
        lst = [{"code": None, "name": nm, "count": n} for nm, n in cnt.items()]
        lst.sort(key=lambda x: x["count"], reverse=True)
        sigungu[s] = lst

    idx = {"provinces": provinces, "sigungu": sigungu, "error": _pet_cache.get("error")}
    _pet_cache["index"] = idx
    return idx


def pets_in_region(prov_short, sigungu=None, content_type=None, limit=60):
    """캐시된 반려동물 전량에서 '주소'로 도/시군구(+업종) 필터링해 norm_place 리스트 반환.
       시군구가 주어지면 접미사 정규화 후 '정확히' 일치하는 곳만 담는다
       (도 단위로 임의 확장하지 않음 → 광진구 선택 시 용산구가 섞이는 버그 방지)."""
    out = []
    want = (sigungu or "").strip() or None
    ct = str(content_type) if content_type else None
    for it in load_all_pets():
        short, code, sig = addr_to_region(it.get("addr1"))
        if short != prov_short:
            continue
        if want and not sig_match(sig, want):        # 고른 시군구와 정확히 일치할 때만
            continue
        if ct and str(it.get("contenttypeid")) != ct:
            continue
        out.append(norm_place(it))
        if len(out) >= limit:
            break
    return out


def load_all_camps():
    """고캠핑 basedList 전량을 한 번만 받아 캐시한다."""
    if _camp_cache["all"] is not None:
        return _camp_cache["all"]
    if not TOURAPI_KEY:
        _camp_cache["all"] = []
        _camp_cache["error"] = "NO_KEY"
        return []
    all_items, page = [], 1
    while page <= 12:
        res = tour_get(GOCAMP, "basedList", {"numOfRows": 1000, "pageNo": page})
        if res.get("error"):
            _camp_cache["error"] = res.get("error")
            _camp_cache["raw"] = res.get("raw")
            break
        items = res.get("items", [])
        if not items:
            break
        all_items.extend(items)
        if len(items) < 1000:
            break
        page += 1
    _camp_cache["all"] = all_items
    _camp_cache["fetched"] = len(all_items)
    return all_items


def build_camp_region_index():
    """
    고캠핑 데이터로 '반려동물 동반 가능한 캠핑장이 있는' 시/도·시/군/구 목록을 만든다.
    (반려동반 API가 아니라 캠핑 API 기준으로 지역을 분배)
    """
    prov_count = Counter()
    prov_code = {}
    sig_count = {}   # short -> Counter(sigunguNm)
    pet_ok = 0
    for it in load_all_camps():
        if camp_verdict((it.get("animalCmgCl") or "").strip()) not in ("ok", "conditional"):
            continue   # 동반 가능한 캠핑장만 집계
        pet_ok += 1
        short, code = map_doname(it.get("doNm"))
        if not short:
            continue
        prov_count[short] += 1
        prov_code[short] = code
        sig_nm = (it.get("sigunguNm") or "").strip()
        if sig_nm:
            sig_count.setdefault(short, Counter())[sig_nm] += 1
    _camp_cache["pet_ok"] = pet_ok

    provinces = [{"name": s, "code": prov_code[s], "count": n}
                 for s, n in prov_count.items()]
    provinces.sort(key=lambda p: p["count"], reverse=True)

    sigungu = {}
    for s, cnt in sig_count.items():
        lst = [{"code": None, "name": nm, "count": n} for nm, n in cnt.items()]
        lst.sort(key=lambda x: x["count"], reverse=True)
        sigungu[s] = lst
    return {"provinces": provinces, "sigungu": sigungu, "error": _camp_cache["error"]}


def get_camp_index():
    if _region_cache["camp"] is None:
        _region_cache["camp"] = build_combined_camp_region_index()
    return _region_cache["camp"]

# 이 개수 이상의 반려동물 동반 장소가 있어야 지역 목록에 노출한다.
# (1 = 한 곳이라도 있으면 표시. 더 크게 잡으면 목록이 더 짧아진다.)
MIN_PET_PLACES = 1


def pet_place_count(area_code, sigungu_code=None):
    """
    해당 지역의 반려동물 동반 장소 총 개수(totalCount)를 반환.
    키 미설정 시 None, 오류 시 0.
    """
    if not TOURAPI_KEY:
        return None
    params = {
        "serviceKey": TOURAPI_KEY, "MobileOS": "ETC", "MobileApp": "withgaegae",
        "_type": "json", "areaCode": area_code, "numOfRows": 1, "pageNo": 1,
    }
    if sigungu_code:
        params["sigunguCode"] = sigungu_code
    try:
        r = requests.get(f"{PET_SVC}/areaBasedList2", params=params, timeout=8)
        r.raise_for_status()
        body = r.json().get("response", {}).get("body", {})
        return int(body.get("totalCount", 0) or 0)
    except Exception as e:
        print(f"[pet_place_count ERROR] area={area_code}: {e}")
        return 0


@app.route('/api/regions/provinces', methods=['POST'])
def regions_provinces():
    """
    반려동물 동반 장소가 있는 시/도만 반환.
    source='camp' 이면 고캠핑 기준, 그 외(기본 'pet')는 반려동반 여행 API 기준.
    """
    source = (request.json or {}).get("source", "pet")
    if not TOURAPI_KEY:
        return jsonify({"success": True, "no_key": True, "provinces": []})

    if source == "camp":
        idx = get_camp_index()
        resp = {"success": True, "source": "camp", "provinces": idx["provinces"]}
        if not idx["provinces"]:
            resp["camp_error"] = _camp_cache.get("error") or "EMPTY"
            resp["hint"] = "고캠핑 API 응답이 비어 있습니다. /api/debug/api 로 원인을 확인하세요."
        return jsonify(resp)

    # pet: areacode가 대부분 비어 있어, 전량을 주소로 분류한 인덱스를 사용(전건 동반 가능)
    idx = build_pet_region_index()
    resp = {"success": True, "source": "pet", "provinces": idx["provinces"]}
    if not idx["provinces"]:
        resp["error"] = _pet_cache.get("error") or "EMPTY"
        resp["hint"] = "반려동물 동반여행 API 응답이 비어 있습니다. /api/debug/api 로 원인을 확인하세요."
    return jsonify(resp)


@app.route('/api/regions/sigungu', methods=['POST'])
def regions_sigungu():
    """해당 시/도에서 반려동물 동반 장소가 있는 시/군/구만 반환. source 분기."""
    data = request.json or {}
    source = data.get("source", "pet")
    try:
        area_code = int(data.get("area_code"))
    except (TypeError, ValueError):
        return jsonify({"success": False, "message": "지역코드 오류"}), 400
    if not TOURAPI_KEY:
        return jsonify({"success": True, "no_key": True, "sigungu": []})

    if source == "camp":
        short = next((s for s, c in AREA_CODE.items() if c == area_code), None)
        sig = get_camp_index()["sigungu"].get(short, [])
        return jsonify({"success": True, "source": "camp", "sigungu": sig})

    # pet: 주소로 만든 시군구 인덱스 사용
    short = SHORT_BY_CODE.get(area_code)
    sig = build_pet_region_index()["sigungu"].get(short, [])
    return jsonify({"success": True, "source": "pet", "sigungu": sig})


# =====================================================================
#  진단(디버그) — 브라우저에서 열어 키/서비스 상태를 바로 확인
# =====================================================================

@app.route('/api/debug/api', methods=['GET'])
def debug_api():
    """반려동반·국문관광·고캠핑 세 서비스가 이 키로 실제 응답하는지 점검한다."""
    key = TOURAPI_KEY or ""
    masked = (key[:4] + "…" + key[-4:]) if len(key) >= 8 else ("(설정됨)" if key else "(미설정)")

    def probe(base, op, params):
        res = tour_get(base, op, params)
        return {"ok": (not res.get("error") and not res.get("_no_key")),
                "error": res.get("error"), "http_status": res.get("http_status"),
                "total": res.get("total"), "raw": res.get("raw")}

    pet = probe(PET_SVC, "areaBasedList2", {"areaCode": 39, "numOfRows": 1, "pageNo": 1})
    kor = probe(KOR_SVC, "searchKeyword2", {"keyword": "카페", "numOfRows": 1, "pageNo": 1})
    camp = probe(GOCAMP, "basedList", {"numOfRows": 1, "pageNo": 1})

    if not key:
        hint = ".env에 TOURAPI_KEY가 없습니다. load_dotenv()가 .env를 읽는지, 변수명이 정확한지 확인하세요."
    elif not (pet["ok"] or kor["ok"] or camp["ok"]):
        hint = "셋 다 실패 → 키가 'Encoding' 키일 가능성이 큽니다. data.go.kr에서 'Decoding' 키를 복사해 .env에 넣으세요."
    elif not camp["ok"]:
        hint = "고캠핑만 실패 → data.go.kr에서 '한국관광공사_고캠핑' 서비스를 별도로 '활용신청'해야 합니다(승인까지 시간이 걸릴 수 있음)."
    else:
        hint = "세 서비스 모두 정상입니다."

    return jsonify({"key_set": bool(key), "key_hint": masked,
                    "pet_service": pet, "kor_service": kor, "gocamping": camp,
                    "hint": hint})


@app.route('/api/debug/camp', methods=['GET'])
def debug_camp():
    """캠핑 지역 인덱스 상태 점검. ?reset=1 로 캐시를 비우고 다시 조회한다."""
    if request.args.get("reset"):
        _camp_cache["all"] = None
        _camp_cache["error"] = None
        _camp_cache["raw"] = None
        _region_cache["camp"] = None
    idx = get_camp_index()
    return jsonify({
        "fetched_camps": _camp_cache.get("fetched"),      # 받아온 전체 캠핑장 수
        "pet_ok_camps": _camp_cache.get("pet_ok"),        # 그중 동반 가능
        "province_count": len(idx["provinces"]),
        "error": _camp_cache.get("error"),
        "raw": _camp_cache.get("raw"),
        "provinces": idx["provinces"],
    })


@app.route('/api/debug/pet', methods=['GET'])
def debug_pet():
    """반려동물 주소기반 지역 인덱스 점검.
       ?reset=1  : 메모리 + 디스크 캐시(pets_cache.json)를 지우고 API에서 다시 조회.
       fetched_pets(전량) 합계가 대략 9,694에 근접하는지 확인용."""
    if request.args.get("reset"):
        _pet_cache["all"] = None
        _pet_cache["index"] = None
        _pet_cache["error"] = None
        _pet_cache["complete"] = False
        try:
            if os.path.exists(PET_CACHE_FILE):
                os.remove(PET_CACHE_FILE)
        except Exception as e:
            print(f"[pets_cache] 삭제 실패: {e}")
    idx = build_pet_region_index()
    total_in_index = sum(p["count"] for p in idx["provinces"])
    return jsonify({
        "fetched_pets": _pet_cache.get("fetched"),     # 받아온 반려동물 전체 건수(≈9,694)
        "complete": _pet_cache.get("complete"),        # 전량 로딩 완료 여부
        "cache_file": PET_CACHE_FILE,
        "cache_file_exists": os.path.exists(PET_CACHE_FILE),
        "province_count": len(idx["provinces"]),
        "sum_by_province": total_in_index,             # 주소로 분류된 합계
        "error": _pet_cache.get("error"),
        "provinces": idx["provinces"],
    })


# =====================================================================
#  고캠핑 정보 조회 (캠핑 갈래 전용)
# =====================================================================

def camp_search(keyword, rows=30, dog=None):
    res = tour_get(GOCAMP, "searchList", {
        "keyword": keyword, "numOfRows": rows, "pageNo": 1,
    })
    return [norm_camp(it, dog) for it in res.get("items", [])]


def camps_in_region(prov_short, sigungu=None, dog=None):
    """고캠핑 전량에서 도/시군구로 필터링."""
    out = []
    want = (sigungu or "").strip() or None
    for it in load_all_camps():
        short, _ = map_doname(it.get("doNm"))
        if short != prov_short:
            continue
        if want and not sig_match(it.get("sigunguNm"), want):
            continue
        out.append(norm_camp(it, dog))
    return out


def pet_camps_in_region(prov_short, sigungu=None):
    """반려동물 동반여행 API에서 캠핑 관련 장소를 지역별로 가져온다.

    (수정) 이전에는 content_type(숙박32/레포츠28)으로 지역 내 최대 80건을 먼저 자른 뒤
    캠핑 키워드를 걸렀다. 그 탓에 숙박 장소가 많은 지역(예: 서울)에서는 캠핑장이
    80건 상한에 밀려 누락됐고, 숙박/레포츠가 아닌 유형의 캠핑장도 제외됐다.
    이제는 지역 내 전량을 '캠핑 키워드'로 직접 필터링해 콘텐츠 유형·건수 상한과
    무관하게 지역의 캠핑 장소를 모두 담는다."""
    camping_words = ("캠핑", "야영", "오토캠", "글램핑", "카라반")
    want = (sigungu or "").strip() or None
    out, seen = [], set()
    for it in load_all_pets():
        title = it.get("title") or ""
        if not any(k in title for k in camping_words):
            continue
        short, _code, sig = addr_to_region(it.get("addr1"))
        if short != prov_short:
            continue
        if want and not sig_match(sig, want):
            continue
        key = _name_key(title)
        if key and key not in seen:
            seen.add(key)
            out.append(norm_place(it))
    return out


def _same_camp(a, b):
    """두 API의 같은 캠핑장 여부를 이름/주소로 비교한다."""
    from difflib import SequenceMatcher
    an, bn = _name_key(a.get("title")), _name_key(b.get("title"))
    aa, ba = _address_key(a.get("addr")), _address_key(b.get("addr"))
    if an and bn and (an == bn or an in bn or bn in an):
        return True
    if aa and ba and aa == ba:
        return True
    if an and bn and aa and ba:
        name_score = SequenceMatcher(None, an, bn).ratio()
        addr_score = SequenceMatcher(None, aa, ba).ratio()
        return name_score >= 0.82 and addr_score >= 0.65
    return False


def merge_camping_sources(prov_short, sigungu=None, dog=None, limit=40):
    """고캠핑 + 반려동물 동반여행 API를 합친다.
    두 API에 같은 캠핑장이 있으면 반려동물 동반여행 API의 장소/동반 정보를 우선한다."""
    camp_items = camps_in_region(prov_short, sigungu, dog) if prov_short else []
    pet_items = pet_camps_in_region(prov_short, sigungu) if prov_short else []

    # 반려동물 API 장소는 상세 API로 다시 판정한다.
    if pet_items:
        with ThreadPoolExecutor(max_workers=8) as ex:
            pet_items = list(ex.map(lambda p: _enrich_one(p, dog), pet_items[:80]))

    merged = []
    used_pet = set()

    for camp in camp_items:
        match_idx = next((i for i, pet in enumerate(pet_items)
                          if i not in used_pet and _same_camp(camp, pet)), None)
        if match_idx is not None:
            # 같은 장소가 두 API에 있으면 PET API 결과를 기본값으로 사용.
            pet = dict(pet_items[match_idx])
            used_pet.add(match_idx)
            pet["source"] = "pet"
            pet["source_label"] = "반려동물 동반여행 API 우선"
            # PET API에 없는 지도/사진/홈페이지 등은 고캠핑 값을 보조로 사용.
            for key in ("tel", "mapx", "mapy", "image", "homepage"):
                if not pet.get(key) and camp.get(key):
                    pet[key] = camp[key]
            pet["induty"] = camp.get("induty", "")
            pet["facility"] = camp.get("facility", "")
            pet["intro"] = pet.get("overview") or camp.get("intro", "")
            merged.append(pet)
        else:
            camp["source"] = "gocamping"
            camp["source_label"] = "고캠핑 API"
            merged.append(camp)

    # 고캠핑에 없고 반려동물 동반여행 API에만 있는 캠핑장도 추가.
    for i, pet in enumerate(pet_items):
        if i in used_pet:
            continue
        pet["source"] = "pet"
        pet["source_label"] = "반려동물 동반여행 API"
        pet["intro"] = pet.get("overview", "")
        merged.append(pet)

    return merged[:limit]


def build_combined_camp_region_index():
    """두 캠핑 API의 지역 목록을 합친다. 어느 한 API에만 있어도 지역을 표시한다."""
    base = build_camp_region_index()
    prov = {p["name"]: dict(p) for p in base.get("provinces", [])}
    sig = {k: {x["name"]: dict(x) for x in v} for k, v in base.get("sigungu", {}).items()}

    camping_words = ("캠핑", "야영", "오토캠", "글램핑", "카라반")
    for it in load_all_pets():
        if str(it.get("contenttypeid")) not in (str(CT["stay"]), str(CT["leports"])):
            continue
        title = it.get("title") or ""
        if not any(k in title for k in camping_words):
            continue
        short, code, addr_sig = addr_to_region(it.get("addr1"))
        if not short:
            continue
        if short not in prov:
            prov[short] = {"name": short, "code": code, "count": 1}
        else:
            prov[short]["count"] = max(prov[short].get("count", 1), 1)
        if addr_sig:
            sig.setdefault(short, {})
            sig[short].setdefault(addr_sig, {"code": None, "name": addr_sig, "count": 1})

    provinces = list(prov.values())
    provinces.sort(key=lambda x: x.get("count", 0), reverse=True)
    sigungu = {k: list(v.values()) for k, v in sig.items()}
    return {"provinces": provinces, "sigungu": sigungu, "error": base.get("error")}


@app.route('/api/camp/area', methods=['POST'])
def camp_area():
    """[캠핑-지역] 고캠핑과 반려동물 동반여행 API의 캠핑 데이터를 함께 조회한다."""
    data = request.json or {}
    region = (data.get("region") or "").strip()
    if not region:
        return jsonify({"success": False, "message": "지역을 선택해주세요."}), 400
    if not TOURAPI_KEY:
        return jsonify({"success": True, "no_key": True, "camps": []})

    parts = region.split()
    prov_short = short_from_text(region)
    sigungu = parts[1] if len(parts) > 1 else None
    dog = representative_dog(data.get("dogs"))

    camps = merge_camping_sources(prov_short, sigungu, dog, 50) if prov_short else []
    if not camps and not sigungu:
        camps = camp_search(region, 30, dog)

    camps = [c for c in camps if c.get("verdict") in ("ok", "conditional", "check")]
    order = {"ok": 0, "conditional": 1, "check": 1, "no_info": 2}
    camps.sort(key=lambda c: order.get(c.get("verdict"), 9))
    return jsonify({"success": True, "no_key": False, "camps": camps[:40]})


@app.route('/api/camp/verify', methods=['POST'])
def camp_verify():
    """[캠핑-지정] 캠핑장 이름으로 확인. 띄어쓰기/오타에 관대하게 검색."""
    data = request.json or {}
    name = (data.get("name") or "").strip()
    if not name:
        return jsonify({"success": False, "message": "캠핑장 이름을 입력해주세요."}), 400
    if not TOURAPI_KEY:
        return jsonify({"success": True, "no_key": True, "camp": None})

    dog = representative_dog(data.get("dogs"))
    # 고캠핑 + 반려동물 동반여행 API 양쪽에서 이름을 찾는다.
    variants = [name]
    if " " in name:
        variants += [name.replace(" ", ""), max(name.split(), key=len)]

    pool = {}
    for kw in variants:
        for c in camp_search(kw, 30, dog):
            pool[_name_key(c["title"])] = c

        for it in load_all_pets():
            if str(it.get("contenttypeid")) not in (str(CT["stay"]), str(CT["leports"])):
                continue
            title = it.get("title") or ""
            if _name_key(kw) in _name_key(title) or _name_key(title) in _name_key(kw):
                pool[_name_key(title)] = norm_place(it)

        if pool:
            break

    # 같은 장소가 양쪽 API에 있으면 반려동물 API 결과로 교체한다.
    cand=[]
    for key, c in pool.items():
        pet_match = next((p for p in pool.values()
                          if p is not c and p.get("contentid") and _same_camp(c, p)), None)
        if pet_match:
            c = pet_match
        if c.get("contentid"):
            c = _enrich_one(c, dog)
        cand.append(c)

    target = _name_key(name)
    best = next((c for c in cand
                 if target in _name_key(c.get("title"))
                 or _name_key(c.get("title")) in target), None)

    if best:
        return jsonify({"success": True, "found": True, "camp": best,
                        "others": [c for c in cand if c is not best][:4]})
    if cand:
        return jsonify({"success": True, "found": False, "candidates": cand[:6],
                        "message": f"'{name}'과 정확히 일치하는 캠핑장을 못 찾았어요. 비슷한 후보를 보여드릴게요."})
    return jsonify({"success": True, "found": False, "candidates": [],
                    "message": f"'{name}' 캠핑장을 찾지 못했어요. '지역으로 찾기'로 근처 캠핑장을 추천받아 보세요."})


# =====================================================================
#  확정 일정 저장
# =====================================================================

@app.route('/api/trip/save', methods=['POST'])
def trip_save():
    """여행 자동저장/확정 저장. id가 있으면 기존 여행을 갱신하고, 없으면 새 여행을 만든다."""
    user = get_current_user()
    if not user:
        return jsonify({"success": False, "message": "로그인이 필요합니다."}), 401

    data = request.json or {}
    title = (data.get("title") or "반려견 동반 여행").strip()
    doc = {
        "user_id": user["user_id"],
        "title": title,
        "type": data.get("type", "plan"),
        "start": data.get("start", ""),
        "end": data.get("end", ""),
        "dogs": data.get("dogs", []),
        "stops": data.get("stops", []),
        "region": data.get("region", ""),
        "region_do": data.get("region_do", ""),
        "area_code": data.get("area_code"),
        "sigungu_code": data.get("sigungu_code"),
        "sigungu_name": data.get("sigungu_name"),
        "status": "planned",
        "done_override": False,
        "progress": 100 if data.get("confirmed") else (10 if not data.get("stops") else min(90, 10 + len(data.get("stops", []))*10)),
        "confirmed": bool(data.get("confirmed", False)),
    }

    tid = data.get("id")
    if tid:
        try:
            res = db.travel.update_one(
                {"_id": ObjectId(tid), "user_id": user["user_id"]},
                {"$set": doc}
            )
            if res.matched_count:
                return jsonify({"success": True, "id": tid, "updated": True})
        except Exception:
            pass

    doc["created"] = datetime.now().strftime("%Y-%m-%d %H:%M")
    res = db.travel.insert_one(doc)
    return jsonify({"success": True, "id": str(res.inserted_id), "updated": False})


@app.route('/api/trip/complete', methods=['POST'])
def trip_complete():
    user = get_current_user()
    if not user:
        return jsonify({"success": False, "message": "로그인이 필요합니다."}), 401
    tid = (request.json or {}).get("id")
    try:
        db.travel.update_one(
            {"_id": ObjectId(tid), "user_id": user["user_id"]},
            {"$set": {"status": "done", "done_override": True, "progress": 100}}
        )
    except Exception:
        return jsonify({"success": False, "message": "잘못된 요청입니다."}), 400
    return jsonify({"success": True})


@app.route('/api/trip/update', methods=['POST'])
def trip_update():
    """여행 이름·날짜 수정."""
    user = get_current_user()
    if not user:
        return jsonify({"success": False, "message": "로그인이 필요합니다."}), 401
    data = request.json or {}
    tid = data.get("id")
    fields = {}
    for k in ("title", "start", "end"):
        if data.get(k) is not None:
            fields[k] = data.get(k)
    if isinstance(data.get("stops"), list):
        fields["stops"] = data.get("stops")
    if not fields:
        return jsonify({"success": False, "message": "수정할 내용이 없습니다."}), 400
    try:
        db.travel.update_one({"_id": ObjectId(tid), "user_id": user["user_id"]},
                             {"$set": fields})
    except Exception:
        return jsonify({"success": False, "message": "잘못된 요청입니다."}), 400
    return jsonify({"success": True})


@app.route('/api/trip/delete', methods=['POST'])
def trip_delete():
    user = get_current_user()
    if not user:
        return jsonify({"success": False, "message": "로그인이 필요합니다."}), 401
    tid = (request.json or {}).get("id")
    try:
        db.travel.delete_one({"_id": ObjectId(tid), "user_id": user["user_id"]})
    except Exception:
        return jsonify({"success": False, "message": "잘못된 요청입니다."}), 400
    return jsonify({"success": True})


# =====================================================================
#  기존 인증/계정 API (유지)
# =====================================================================

@app.route('/api/check-id', methods=['POST'])
def check_id():
    data = request.json
    user_id = data.get('user_id')
    if not user_id:
        return jsonify({"success": False, "message": "아이디를 입력해주세요."}), 400
    if db.users.find_one({"user_id": user_id}):
        return jsonify({"success": False, "message": "이미 사용 중인 아이디입니다."})
    return jsonify({"success": True, "message": "사용 가능한 아이디입니다."})

@app.route('/api/signup', methods=['POST'])
def signup():
    data = request.json or {}
    user_id = (data.get('user_id') or '').strip()
    password = data.get('password') or ''
    name = (data.get('name') or '').strip()

    if not name or not user_id or not password:
        return jsonify({"success": False, "message": "이름, 아이디, 비밀번호를 모두 입력해주세요."}), 400

    if db.users.find_one({"user_id": user_id}):
        return jsonify({"success": False, "message": "중복된 아이디입니다."}), 400

    new_user = {
        "user_id": user_id,
        "password": generate_password_hash(password),
        "name": name,
        "dogs": [],          # 빈 상태로 시작 (반려견은 마이페이지에서 추가)
        "trips": [],
        "ongoing_trip": None
    }
    db.users.insert_one(new_user)
    session['user_id'] = user_id
    return jsonify({"success": True})

@app.route('/api/add-dog', methods=['POST'])
def add_dog():
    user = get_current_user()
    if not user:
        return jsonify({"success": False, "message": "로그인이 필요합니다."}), 401
    data = request.json
    dog_name = (data.get('name') or '').strip()
    breed = (data.get('breed') or '').strip()
    weight = (data.get('weight') or '').strip()
    desc = (data.get('desc') or '').strip()
    size = (data.get('size') or '').strip()          # small|medium|large (선택)
    guide = bool(data.get('guide'))                  # 맹인 안내견 여부

    # 견종/무게로 표시용 desc 생성 (예: "리트리버 · 18kg")
    if not desc and (breed or weight):
        w = weight
        if w and not str(w).lower().endswith('kg'):
            w = f"{w}kg"
        desc = " · ".join([x for x in [breed, w] if x])

    # 크기/안내견 태그를 desc 끝에 덧붙임 (예: "리트리버 · 30kg · 대형견")
    tag = ""
    if guide:
        tag = "안내견"
    elif size in ("small", "medium", "large"):
        tag = {"small": "소형견", "medium": "중형견", "large": "대형견"}[size]
    if tag:
        desc = f"{desc} · {tag}" if desc else tag

    if not dog_name or not desc:
        return jsonify({"success": False, "message": "이름·견종·무게를 모두 입력해주세요."}), 400

    dog_doc = {"name": dog_name, "breed": breed, "weight": weight,
               "size": size, "guide": guide, "desc": desc}
    photo = data.get('photo')
    if photo:
        dog_doc["photo"] = photo
    db.users.update_one({"user_id": user['user_id']}, {"$push": {"dogs": dog_doc}})
    return jsonify({"success": True})

@app.route('/api/update-dog', methods=['POST'])
def update_dog():
    """반려견 정보 수정 + 프로필 사진(base64 data URL) 저장."""
    user = get_current_user()
    if not user:
        return jsonify({"success": False, "message": "로그인이 필요합니다."}), 401
    data = request.json or {}
    try:
        idx = int(data.get("index"))
    except (TypeError, ValueError):
        return jsonify({"success": False, "message": "잘못된 요청입니다."}), 400
    dogs = user.get("dogs", [])
    if idx < 0 or idx >= len(dogs):
        return jsonify({"success": False, "message": "반려견을 찾을 수 없습니다."}), 400

    name = (data.get("name") or "").strip()
    breed = (data.get("breed") or "").strip()
    weight = (data.get("weight") or "").strip()
    size = (data.get("size") or "").strip()
    guide = bool(data.get("guide"))
    photo = data.get("photo")   # data URL(설정) / "" (제거) / None (변경 안 함)
    if not name:
        return jsonify({"success": False, "message": "이름을 입력해주세요."}), 400

    w = weight
    if w and not str(w).lower().endswith("kg"):
        w = f"{w}kg"
    desc = " · ".join([x for x in [breed, w] if x])
    tag = "안내견" if guide else {"small": "소형견", "medium": "중형견", "large": "대형견"}.get(size, "")
    if tag:
        desc = f"{desc} · {tag}" if desc else tag

    dog = dogs[idx]
    dog.update({"name": name, "breed": breed, "weight": weight,
                "size": size, "guide": guide, "desc": desc})
    if photo is not None:
        dog["photo"] = photo
    db.users.update_one({"user_id": user["user_id"]}, {"$set": {f"dogs.{idx}": dog}})
    return jsonify({"success": True})

@app.route('/api/delete-dog', methods=['POST'])
def delete_dog():
    user = get_current_user()
    if not user:
        return jsonify({"success": False, "message": "로그인이 필요합니다."}), 401
    try:
        idx = int((request.json or {}).get("index"))
    except (TypeError, ValueError):
        return jsonify({"success": False, "message": "잘못된 요청입니다."}), 400
    dogs = user.get("dogs", [])
    if idx < 0 or idx >= len(dogs):
        return jsonify({"success": False, "message": "반려견을 찾을 수 없습니다."}), 400
    dogs.pop(idx)
    db.users.update_one({"user_id": user["user_id"]}, {"$set": {"dogs": dogs}})
    return jsonify({"success": True})

@app.route('/api/change-pw', methods=['POST'])
def change_pw():
    user = get_current_user()
    if not user: return jsonify({"success": False, "message": "로그인 필요"}), 401
    data = request.json or {}
    current_pw = data.get('current_password') or ''
    new_pw = data.get('new_password') or ''
    if not current_pw or not new_pw:
        return jsonify({"success": False, "message": "기존 비밀번호와 새 비밀번호를 모두 입력해 주세요."}), 400
    if not check_password_hash(user['password'], current_pw):
        return jsonify({"success": False, "message": "기존 비밀번호가 일치하지 않습니다."}), 400
    if current_pw == new_pw:
        return jsonify({"success": False, "message": "기존과 다른 새 비밀번호를 입력해 주세요."}), 400
    db.users.update_one({"user_id": user['user_id']}, {"$set": {"password": generate_password_hash(new_pw)}})
    return jsonify({"success": True, "message": "비밀번호가 성공적으로 변경되었습니다."})

@app.route('/api/delete-account', methods=['POST'])
def delete_account():
    user = get_current_user()
    if not user: return jsonify({"success": False, "message": "로그인 필요"}), 401
    data = request.json
    password = data.get('password')
    if check_password_hash(user['password'], password):
        db.users.delete_one({"user_id": user['user_id']})
        session.pop('user_id', None)
        return jsonify({"success": True})
    return jsonify({"success": False, "message": "비밀번호가 일치하지 않습니다."})

@app.route('/api/login', methods=['POST'])
def login():
    data = request.json
    user_id = data.get('user_id')
    password = data.get('password')
    user = db.users.find_one({"user_id": user_id})
    if user and check_password_hash(user['password'], password):
        session['user_id'] = user_id
        return jsonify({"success": True})
    return jsonify({"success": False, "message": "계정 정보 불일치"}), 401

@app.route('/api/logout', methods=['POST'])
def logout_api():
    session.pop('user_id', None)
    return jsonify({"success": True})

@app.route('/api/places', methods=['GET'])
def get_places():
    places = list(db.places.find({}, {"_id": 0}))
    return jsonify(places)


@app.route('/api/debug/camp-region', methods=['GET'])
def debug_camp_region():
    """특정 지역의 캠핑 병합 결과를 진단한다.
       예: /api/debug/camp-region?region=서울  (또는 ?region=서울 강남구)"""
    region = (request.args.get("region") or "").strip()
    if not region:
        return jsonify({"success": False,
                        "message": "region 쿼리를 넣어주세요. 예: ?region=서울"}), 400
    parts = region.split()
    prov_short = short_from_text(region)
    sigungu = parts[1] if len(parts) > 1 else None
    if not prov_short:
        return jsonify({"success": False,
                        "message": f"'{region}' 지역을 인식하지 못했어요."}), 400
    camp_items = camps_in_region(prov_short, sigungu)          # 고캠핑
    pet_items = pet_camps_in_region(prov_short, sigungu)       # 반려동물 동반 API의 캠핑
    merged = merge_camping_sources(prov_short, sigungu, None, 50)
    vc = Counter(c.get("verdict") for c in merged)
    return jsonify({
        "region": region, "prov_short": prov_short, "sigungu": sigungu,
        "gocamping_count": len(camp_items),
        "pet_camping_count": len(pet_items),
        "pet_camping_titles": [p.get("title") for p in pet_items][:30],
        "merged_count": len(merged),
        "merged_verdicts": dict(vc),
        "merged_titles": [(c.get("title"), c.get("verdict")) for c in merged][:40],
    })


if __name__ == '__main__':
    app.run(host="0.0.0.0", debug=True, port=5000)
