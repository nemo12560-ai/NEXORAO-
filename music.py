"""
ربات موزیک روبیکا + پنل مدیریت آهنگ‌ها (همه در یک فایل)

نصب:   pip install rubpy yt-dlp flask   (و نصب ffmpeg)
اجرا:  PANEL_PASSWORD=رمز-دلخواه USE_YOUTUBE=0 python music.py
پنل:   http://127.0.0.1:8080

متغیرها: PANEL_PASSWORD (الزامی) | USE_YOUTUBE=0 (فقط کتابخانه) | MUSIC_PROXY=socks5://127.0.0.1:10808

دستورهای گروه:
  پخش (ریپلای روی فایل) | پخش <لینک> | پخش آهنگ <اسم> | پخش <شماره> | پلی لیست
  تنظیم صدا <0-200> | تنظیم سرعت <0.5-2> | کال | توقف | پایان کال  (کال نیاز به aiortc دارد)
  محافظت (ادمین): قفل/بازکردن <لینک|اسپم|عکس|ویدیو|فایل|ویس|استیکر|فوروارد> | سکوت [دقیقه] / رفع سکوت / اخراج / اخطار / تشخیص (ریپلای)
  پروفایل: آمار | آمار گروه | ثبت لقب <لقب> | ثبت اصل <اسم> <سن> <شهر>  (ادمین با ریپلای برای دیگران)
  بازی: بازی حدس عدد | بازی کوییز | بازی معما | بازی سنگ کاغذ قیچی | جواب | پایان بازی | جدول امتیاز
  دسترسی: «guid من» | (ادمین) «افزودن» / «ادمین» / «حذف» با ریپلای | «لیست مجازها»
"""
import asyncio
import atexit
from datetime import datetime, timedelta, timezone
import difflib
import hmac
import inspect
import json
import os
import re
import secrets
import tempfile
import random
import threading
import time
import traceback
import uuid
from collections import defaultdict, deque
from functools import wraps

import yt_dlp
from flask import (Flask, abort, redirect, render_template_string, request,
                   send_from_directory, session, url_for)
from rubpy import Client, filters
from rubpy.types import Updates

# ======================= کتابخانه‌ی آهنگ‌ها =======================
LIB_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "library")
INDEX = os.path.join(LIB_DIR, "index.json")
ALLOWED = {".mp3", ".m4a", ".ogg", ".wav", ".flac", ".aac"}
os.makedirs(LIB_DIR, exist_ok=True)


def norm(s: str) -> str:
    """یکسان‌سازی متن فارسی برای جستجو"""
    s = s.lower()
    s = s.replace("ي", "ی").replace("ك", "ک").replace("‌", " ")
    s = re.sub(r"[ً-ٟـ]", "", s)  # اعراب و کشیده
    s = re.sub(r"[^\w\s]", " ", s)
    return re.sub(r"\s+", " ", s).strip()


def _load() -> list[dict]:
    try:
        with open(INDEX, encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return []


def _save(items: list[dict]) -> None:
    tmp = INDEX + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(items, f, ensure_ascii=False, indent=1)
    os.replace(tmp, INDEX)


def lib_list_all() -> list[dict]:
    return _load()


def lib_add(src_path: str, title: str) -> dict:
    ext = os.path.splitext(src_path)[1].lower()
    if ext not in ALLOWED:
        raise ValueError("فرمت فایل مجاز نیست")
    item = {"id": uuid.uuid4().hex[:10], "title": title.strip() or "بدون نام"}
    item["file"] = item["id"] + ext
    os.replace(src_path, os.path.join(LIB_DIR, item["file"]))
    items = _load()
    items.append(item)
    _save(items)
    return item


def lib_rename(item_id: str, title: str) -> None:
    items = _load()
    for it in items:
        if it["id"] == item_id:
            it["title"] = title.strip() or it["title"]
    _save(items)


def lib_delete(item_id: str) -> None:
    items = _load()
    for it in items:
        if it["id"] == item_id:
            try:
                os.remove(os.path.join(LIB_DIR, it["file"]))
            except FileNotFoundError:
                pass
    _save([it for it in items if it["id"] != item_id])


def path_of(item: dict) -> str:
    return os.path.join(LIB_DIR, item["file"])


def lib_search(query: str, threshold: float = 0.45) -> dict | None:
    """بهترین آهنگ مطابق با متن را برمی‌گرداند: {'title','path',...} یا None"""
    q = norm(query)
    if not q:
        return None
    q_tokens = q.split()
    best, best_score = None, 0.0
    for it in _load():
        t = norm(it["title"])
        if not t:
            continue
        if q == t:
            score = 1.0
        else:
            hit = sum(1 for w in q_tokens if w in t) / len(q_tokens)  # کلمه‌های پیدا شده
            fuzzy = difflib.SequenceMatcher(None, q, t).ratio()
            score = max(hit * 0.9 + (0.1 if q in t else 0), fuzzy)
        if score > best_score:
            best, best_score = it, score
    if best and best_score >= threshold and os.path.exists(path_of(best)):
        return {**best, "path": path_of(best)}
    return None


# ======================= پنل =======================
PASSWORD = os.environ.get("PANEL_PASSWORD")
if not PASSWORD:
    raise SystemExit("اول متغیر PANEL_PASSWORD را تنظیم کنید. مثال:  PANEL_PASSWORD=Music1234 python music.py")

app = Flask(__name__)
app.secret_key = os.environ.get("PANEL_SECRET") or secrets.token_hex(16)
app.config["MAX_CONTENT_LENGTH"] = 500 * 1024 * 1024  # حداکثر حجم هر آپلود


def login_required(f):
    @wraps(f)
    def wrapper(*a, **kw):
        if not session.get("ok"):
            return redirect(url_for("login"))
        return f(*a, **kw)
    return wrapper


def csrf_ok() -> bool:
    return hmac.compare_digest(request.form.get("csrf", ""), session.get("csrf", ""))


PAGE = """<!doctype html><html lang="fa" dir="rtl"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>پنل موزیک</title>
<style>
body{font-family:Tahoma,sans-serif;background:#12141a;color:#e8e8ee;max-width:820px;margin:0 auto;padding:16px}
h1{font-size:20px} .box{background:#1b1e27;border-radius:12px;padding:14px;margin:12px 0}
input,button{font:inherit;padding:8px 10px;border-radius:8px;border:1px solid #333;background:#232733;color:inherit}
button{cursor:pointer;background:#4f46e5;border:0} button.del{background:#b91c1c}
.row{display:flex;gap:8px;align-items:center;flex-wrap:wrap;padding:10px 0;border-bottom:1px solid #2a2e3a}
.row:last-child{border:0} .row input[type=text]{flex:1;min-width:140px} audio{height:32px;max-width:100%}
.muted{color:#8b90a0;font-size:13px}
</style></head><body>
<h1>🎧 پنل موزیک <span class="muted">({{ items|length }} آهنگ)</span></h1>

<div class="box"><form method="post" action="{{ url_for('upload') }}" enctype="multipart/form-data">
<input type="hidden" name="csrf" value="{{ csrf }}">
<input type="file" name="files" multiple accept="audio/*" required>
<button>آپلود</button>
<div class="muted">عنوان از اسم فایل برداشته می‌شود؛ بعداً می‌توانید ویرایشش کنید. ربات با همین عنوان‌ها جستجو می‌کند.</div>
</form></div>

<div class="box"><form method="get">
<input type="text" name="q" value="{{ q }}" placeholder="جستجو در آهنگ‌ها..." style="width:70%">
<button>جستجو</button></form>
{% for it in items %}
<div class="row">
 <form method="post" action="{{ url_for('rename', item_id=it.id) }}" style="display:contents">
  <input type="hidden" name="csrf" value="{{ csrf }}">
  <input type="text" name="title" value="{{ it.title }}">
  <button>ذخیره</button></form>
 <audio controls preload="none" src="{{ url_for('media', fname=it.file) }}"></audio>
 <form method="post" action="{{ url_for('remove', item_id=it.id) }}" onsubmit="return confirm('حذف شود؟')" style="display:contents">
  <input type="hidden" name="csrf" value="{{ csrf }}"><button class="del">حذف</button></form>
</div>
{% else %}<p class="muted">آهنگی پیدا نشد.</p>{% endfor %}</div>
<p><a href="{{ url_for('logout') }}" class="muted">خروج</a></p>
</body></html>"""

LOGIN = """<!doctype html><html lang="fa" dir="rtl"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>ورود</title>
<style>body{font-family:Tahoma;background:#12141a;color:#e8e8ee;display:grid;place-items:center;height:90vh}
input,button{font:inherit;padding:10px;border-radius:8px;border:0;margin:4px}</style></head>
<body><form method="post"><h3>ورود به پنل</h3>
<input type="password" name="password" placeholder="رمز" autofocus>
<button>ورود</button>{% if err %}<p style="color:#f87171">رمز اشتباه است</p>{% endif %}</form></body></html>"""


@app.route("/login", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        if hmac.compare_digest(request.form.get("password", ""), PASSWORD):
            session["ok"] = True
            session["csrf"] = secrets.token_hex(16)
            return redirect(url_for("index"))
        return render_template_string(LOGIN, err=True)
    return render_template_string(LOGIN, err=False)


@app.route("/logout")
def logout():
    session.clear()
    return redirect(url_for("login"))


@app.route("/")
@login_required
def index():
    q = request.args.get("q", "").strip()
    items = lib_list_all()
    if q:
        nq = norm(q)
        items = [i for i in items if nq in norm(i["title"])]
    return render_template_string(PAGE, items=items[::-1], q=q, csrf=session["csrf"])


@app.route("/upload", methods=["POST"])
@login_required
def upload():
    if not csrf_ok():
        abort(400)
    for f in request.files.getlist("files"):
        name, ext = os.path.splitext(f.filename or "")
        if ext.lower() not in ALLOWED:
            continue
        fd, tmp = tempfile.mkstemp(suffix=ext, dir=LIB_DIR)
        os.close(fd)
        f.save(tmp)
        lib_add(tmp, name)
    return redirect(url_for("index"))


@app.route("/rename/<item_id>", methods=["POST"])
@login_required
def rename(item_id):
    if not csrf_ok():
        abort(400)
    lib_rename(item_id, request.form.get("title", ""))
    return redirect(request.referrer or url_for("index"))


@app.route("/delete/<item_id>", methods=["POST"])
@login_required
def remove(item_id):
    if not csrf_ok():
        abort(400)
    lib_delete(item_id)
    return redirect(request.referrer or url_for("index"))


@app.route("/media/<path:fname>")
@login_required
def media(fname):
    return send_from_directory(LIB_DIR, fname)




# ======================= ربات =======================
# USE_YOUTUBE=0 یعنی فقط از کتابخانه‌ی پنل (بدون نیاز به وی‌پی‌ان)
USE_YOUTUBE = os.environ.get("USE_YOUTUBE", "1") != "0"
PLAYLIST_SIZE = 10
MAX_FILE_MB = 50
WORK_DIR = tempfile.mkdtemp(prefix="rubmusic_")

# حالت هر چت: صدا، سرعت، پلی‌لیست (آخرین موزیک‌های پخش‌شده)
state = defaultdict(lambda: {"volume": 50, "speed": 1.0, "playlist": deque(maxlen=PLAYLIST_SIZE)})

bot = Client(name="loop_music_bot")

# ---------- کنترل دسترسی ----------
# فقط این افراد می‌توانند به ربات دستور بدهند:
#   مالک(ها): حساب خود ربات + متغیر OWNER_GUIDS (چند guid با ویرگول) + ادمین‌های ذخیره‌شده
#   کاربران مجاز: با دستور «افزودن» (ریپلای روی پیام فرد) اضافه می‌شوند
# ALLOW_ALL=1 یعنی همه مجازند (برای تست)
ACCESS_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "access.json")
ALLOW_ALL = os.environ.get("ALLOW_ALL") == "1"
OWNER_ENV = {g.strip() for g in os.environ.get("OWNER_GUIDS", "").split(",") if g.strip()}
_warned_sender = False


def _access_load() -> dict:
    try:
        with open(ACCESS_FILE, encoding="utf-8") as f:
            d = json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        d = {}
    d.setdefault("admins", [])
    d.setdefault("users", [])
    return d


def _access_save(d: dict) -> None:
    tmp = ACCESS_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(d, f, ensure_ascii=False, indent=1)
    os.replace(tmp, ACCESS_FILE)


def sender_guid(obj) -> str | None:
    """guid فرستنده‌ی پیام (اسم فیلد بسته به نسخه‌ی rubpy فرق می‌کند)"""
    for name in ("author_guid", "author_object_guid", "sender_guid", "user_guid", "from_guid"):
        v = getattr(obj, name, None)
        if isinstance(v, str) and v:
            return v
    if isinstance(obj, dict):
        for name in ("author_object_guid", "author_guid", "sender_guid"):
            if obj.get(name):
                return obj[name]
    return None


def is_admin(guid: str | None) -> bool:
    if not guid:
        return False
    me = getattr(bot, "guid", None)
    return guid == me or guid in OWNER_ENV or guid in _access_load()["admins"]


def is_allowed(guid: str | None) -> bool:
    if ALLOW_ALL:
        return True
    if not guid:
        return False
    return is_admin(guid) or guid in _access_load()["users"]





# ---------- ابزارها ----------
async def run(*cmd) -> tuple[int, str]:
    p = await asyncio.create_subprocess_exec(
        *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT
    )
    out, _ = await p.communicate()
    return p.returncode, out.decode(errors="ignore")


def ytdlp_download(query_or_url: str) -> tuple[str, str]:
    """دانلود صوت از لینک یا جستجو. خروجی: (مسیر فایل mp3, عنوان)"""
    is_url = re.match(r"https?://", query_or_url) is not None
    target = query_or_url if is_url else f"ytsearch1:{query_or_url}"
    opts = {
        "format": "bestaudio/best",
        "outtmpl": os.path.join(WORK_DIR, "%(id)s.%(ext)s"),
        "noplaylist": True,
        "quiet": True,
        "max_filesize": MAX_FILE_MB * 1024 * 1024,
        # پروکسی/وی‌پی‌ان محلی؛ مثال: set MUSIC_PROXY=socks5://127.0.0.1:10808
        "proxy": os.environ.get("MUSIC_PROXY") or None,
        "postprocessors": [
            {"key": "FFmpegExtractAudio", "preferredcodec": "mp3", "preferredquality": "192"}
        ],
    }
    with yt_dlp.YoutubeDL(opts) as ydl:
        info = ydl.extract_info(target, download=True)
        if "entries" in info:
            info = info["entries"][0]
        path = os.path.splitext(ydl.prepare_filename(info))[0] + ".mp3"
        return path, info.get("title", "music")


async def apply_effects(src: str, volume: int, speed: float) -> str:
    """اعمال صدا (درصد) و سرعت با ffmpeg"""
    if volume == 50 and speed == 1.0:
        return src
    base = os.path.splitext(os.path.basename(src))[0]
    dst = os.path.join(WORK_DIR, f"{base}_v{volume}_s{speed}.mp3")  # کتابخانه دست نمی‌خورد
    # 50% = صدای اصلی، 100% = دو برابر
    filt = f"volume={volume / 50:.2f},atempo={speed}"
    code, out = await run("ffmpeg", "-y", "-i", src, "-filter:a", filt, dst)
    if code != 0:
        raise RuntimeError(out[-300:])
    return dst


# ======================= ویس‌چت (حضور در کال و پخش صدا) =======================
# هشدار: این بخش نسخه‌ی اولیه و آزمایشی است. اسم متدها و فرمت داده‌ها بر اساس API روبیکا حدس زده شده
# و با aiortc (WebRTC) کار می‌کند:  pip install aiortc
# باید روی کامپیوتر/VPS لینوکسی اجرا شود؛ روی ترموکس معمولاً aiortc نصب نمی‌شود.
calls: dict = {}  # guid گروه -> VoiceCall


def _find(obj, key):
    """جستجوی بازگشتی یک کلید در دیکشنری/آبجکت پاسخ"""
    if obj is None:
        return None
    if hasattr(obj, "to_dict"):
        try:
            obj = obj.to_dict()
        except Exception:
            pass
    if isinstance(obj, dict):
        if key in obj and obj[key] not in (None, ""):
            return obj[key]
        for v in obj.values():
            r = _find(v, key)
            if r not in (None, ""):
                return r
    elif isinstance(obj, (list, tuple)):
        for v in obj:
            r = _find(v, key)
            if r not in (None, ""):
                return r
    elif hasattr(obj, "__dict__"):
        return _find(vars(obj), key)
    return None


async def rb_call(api_name: str, **data):
    """صدا زدن یک متد API روبیکا (اول builder، بعد متد snake_case)"""
    snake = re.sub(r"(?<!^)(?=[A-Z])", "_", api_name).lower()
    errors = []
    builder = getattr(bot, "builder", None)
    if builder is not None:
        try:
            r = builder(name=api_name, input=data)
            return await r if inspect.isawaitable(r) else r
        except Exception as e:
            errors.append(f"builder: {str(e)[:100]}")
    fn = getattr(bot, snake, None)
    if fn is not None:
        try:
            r = fn(**data)
            return await r if inspect.isawaitable(r) else r
        except Exception as e:
            errors.append(f"{snake}: {str(e)[:100]}")
    raise RuntimeError(f"{api_name} ناموفق | " + " | ".join(errors))


class VoiceCall:
    def __init__(self, chat_guid: str):
        self.chat_guid = chat_guid
        self.voice_chat_id = None
        self.pc = None
        self.track = None
        self.player = None
        self.tasks = []
        self.self_guid = getattr(bot, "guid", None)
        self.sent_music = 0      # فریم‌های آهنگ ارسال‌شده
        self.sent_silence = 0    # فریم‌های سکوت
        self.log = []            # رویدادهای اتصال
        self.offer_sdp = ""
        self.answer_sdp = ""

    def status(self) -> str:
        pc = self.pc
        lines = [
            f"connection: {getattr(pc, 'connectionState', None)}",
            f"ice: {getattr(pc, 'iceConnectionState', None)} | gathering: {getattr(pc, 'iceGatheringState', None)}",
            f"فریم آهنگ: {self.sent_music} | فریم سکوت: {self.sent_silence}",
            f"player: {'دارد' if self.player else 'ندارد'}",
            "رویدادها: " + " > ".join(self.log[-8:]),
        ]
        keep = ("m=", "a=candidate", "a=rtpmap", "a=ice-lite", "a=setup", "a=sendrecv",
                "a=recvonly", "a=sendonly", "a=inactive", "a=rtcp-mux")
        pick = lambda t: [l for l in t.splitlines() if l.startswith(keep)]
        lines.append("--- offer ---\n" + "\n".join(pick(self.offer_sdp))[:500])
        lines.append("--- answer ---\n" + "\n".join(pick(self.answer_sdp))[:700])
        return "\n".join(lines)

    async def start(self):
        try:
            from aiortc import (AudioStreamTrack, RTCConfiguration,
                                RTCPeerConnection, RTCSessionDescription)
            from aiortc.mediastreams import MediaStreamError
        except ImportError as e:
            raise RuntimeError(f"import aiortc ناموفق: {e}")

        outer = self

        class SwitchTrack(AudioStreamTrack):
            """هر لحظه یا صدای آهنگ جاری یا سکوت می‌فرستد"""
            async def recv(self):
                src = outer.player.audio if outer.player else None
                if src is not None:
                    try:
                        frame = await src.recv()
                        outer.sent_music += 1
                        return frame
                    except MediaStreamError:
                        outer.player = None
                        outer.log.append("track-ended")
                outer.sent_silence += 1
                return await super().recv()

        # ساخت ویس‌چت (اگر از قبل هست، شناسه‌اش را از پاسخ یا خطا بردارید)
        res = await rb_call("createGroupVoiceChat", chat_guid=self.chat_guid)
        self.voice_chat_id = _find(res, "voice_chat_id")
        if not self.voice_chat_id:
            raise RuntimeError(f"voice_chat_id در پاسخ نبود: {str(res)[:200]}")

        # اتصال WebRTC (بدون STUN گوگل تا در ایران گیر نکند)
        self.pc = RTCPeerConnection(RTCConfiguration(iceServers=[]))
        self.track = SwitchTrack()
        self.pc.addTrack(self.track)

        @self.pc.on("connectionstatechange")
        async def _on_conn():
            self.log.append("conn:" + self.pc.connectionState)
            print("connectionState:", self.pc.connectionState)

        @self.pc.on("iceconnectionstatechange")
        async def _on_ice():
            self.log.append("ice:" + self.pc.iceConnectionState)
            print("iceConnectionState:", self.pc.iceConnectionState)
        offer = await self.pc.createOffer()
        await self.pc.setLocalDescription(offer)
        sdp = self.pc.localDescription.sdp
        self.offer_sdp = sdp

        answer = None
        errs = []
        # فرمت SDP را هم خام و هم JSON امتحان می‌کنیم
        for payload in (sdp, json.dumps({"type": "offer", "sdp": sdp})):
            try:
                res = await rb_call(
                    "joinGroupVoiceChat",
                    chat_guid=self.chat_guid,
                    voice_chat_id=self.voice_chat_id,
                    sdp_offer_data=payload,
                    self_object_guid=self.self_guid,
                )
                answer = _find(res, "sdp_answer_data")
                if answer:
                    break
            except Exception as e:
                errs.append(str(e)[:150])
        if not answer:
            raise RuntimeError("join ناموفق: " + " || ".join(errs))
        if isinstance(answer, str) and answer.strip().startswith("{"):
            try:
                answer = json.loads(answer).get("sdp", answer)
            except Exception:
                pass
        self.answer_sdp = answer
        await self.pc.setRemoteDescription(RTCSessionDescription(sdp=answer, type="answer"))
        self.tasks.append(asyncio.create_task(self._heartbeat()))

    async def _heartbeat(self):
        """هر ۲ ثانیه فعالیت و هر ۱۰ ثانیه وضعیت (طبق مستندات RubJS)"""
        n = 0
        while True:
            try:
                await rb_call("sendVoiceChatActivity", chat_guid=self.chat_guid,
                              voice_chat_id=self.voice_chat_id,
                              participant_object_guid=self.self_guid, activity="Speaking")
                if n % 5 == 0:
                    await rb_call("getGroupVoiceChatUpdates", chat_guid=self.chat_guid,
                                  voice_chat_id=self.voice_chat_id)
            except Exception as e:
                if n == 0:
                    print("heartbeat error:", str(e)[:200])
            n += 1
            await asyncio.sleep(2)

    async def play(self, path: str):
        from aiortc.contrib.media import MediaPlayer
        self.player = MediaPlayer(path)

    def stop_track(self):
        self.player = None

    async def leave(self, discard: bool = True):
        for t in self.tasks:
            t.cancel()
        self.player = None
        if self.pc:
            await self.pc.close()
        if discard and self.voice_chat_id:
            try:
                await rb_call("discardGroupVoiceChat", chat_guid=self.chat_guid,
                              voice_chat_id=self.voice_chat_id)
            except Exception as e:
                print("discard error:", str(e)[:200])


# ---------- ارسال و دریافت (وابسته به نسخه rubpy؛ اگر خطا داد فقط همین بخش را تنظیم کنید) ----------
async def _maybe_await(r):
    return await r if inspect.isawaitable(r) else r


async def send_music(update: Updates, path: str, title: str):
    """چند روش ارسال را به ترتیب امتحان می‌کند و خطای هرکدام را گزارش می‌دهد."""
    guid = update.object_guid
    vc = calls.get(guid)
    if vc:  # در کال هستیم: داخل ویس‌چت پخش کن، بدون آپلود فایل
        await vc.play(path)
        return await update.reply(f"🎶 در کال پخش می‌شود: {title}")
    caption = f"🎧 {title}"
    errs = []
    for name in ("send_music", "send_document", "send_file"):
        fn = getattr(bot, name, None)
        if fn is None:
            continue
        for kw in ({"caption": caption, "reply_to_message_id": update.message_id},
                   {"text": caption, "reply_to_message_id": update.message_id},
                   {}):
            try:
                return await _maybe_await(fn(guid, path, **kw))
            except TypeError as e:  # آرگومان‌های این روش با این نسخه نمی‌خواند؛ حالت بعد
                last = f"{name}: {str(e)[:80]}"
                continue
            except Exception as e:
                errs.append(f"{name}: {str(e)[:120]}")
                break
        else:
            errs.append(last)
    raise RuntimeError(" | ".join(errs) or "هیچ متد ارسال فایلی در این نسخه‌ی rubpy پیدا نشد")


async def download_replied_media(update: Updates) -> tuple[str, str] | None:
    replied = await update.get_reply_message()
    if replied is None:
        return None
    dst = os.path.join(WORK_DIR, f"replied_{replied.message_id}.bin")
    result = bot.download(replied, dst)
    if inspect.isawaitable(result):
        result = await result
    # بسته به نسخه‌ی rubpy ممکن است مسیر فایل یا خود محتوا (bytes) برگردد
    if isinstance(result, (bytes, bytearray)):
        with open(dst, "wb") as f:
            f.write(result)
    elif isinstance(result, str) and os.path.exists(result):
        dst = result
    if not os.path.exists(dst) or os.path.getsize(dst) == 0:
        return None
    name = getattr(replied, "file_name", None) or f"replied_{replied.message_id}"
    return dst, os.path.splitext(str(name))[0]


# ---------- منطق اصلی ----------
async def play(update: Updates, chat: dict, source: str | None, title_hint: str = ""):
    msg = await update.reply("⏳ در حال آماده‌سازی...")
    try:
        if source is None:
            got = await download_replied_media(update)
            if not got:
                return await update.reply("روی یک فایل صوتی یا ویدیو ریپلای کن و بگو «پخش»")
            raw, title = got
            # تبدیل به mp3 (برای ویدیو هم کار می‌کند)
            mp3 = os.path.splitext(raw)[0] + ".mp3"
            await run("ffmpeg", "-y", "-i", raw, "-vn", mp3)
            path = mp3
            entry = {"title": title, "src": mp3}
        else:
            # اول کتابخانه‌ی پنل، بعد (در صورت فعال بودن) یوتیوب
            hit = None if re.match(r"https?://", source) else lib_search(source)
            if hit:
                path, title = hit["path"], hit["title"]
            elif USE_YOUTUBE:
                path, title = await asyncio.to_thread(ytdlp_download, source)
            else:
                return await update.reply("❌ این آهنگ در کتابخانه نیست. از پنل اضافه‌اش کنید.")
            entry = {"title": title, "src": path}

        final = await apply_effects(path, chat["volume"], chat["speed"])
        chat["playlist"].appendleft(entry)
        await send_music(update, final, title)
    except Exception as e:
        tb = traceback.format_exc()
        print(tb)
        # خطوط مهم traceback (فقط خطوط مربوط به فایل‌ها) برای اینکه در خود گروه دیده شود
        short = "\n".join(l.strip() for l in tb.splitlines() if l.strip().startswith(("File", "TypeError", "ValueError", "AttributeError", "KeyError", "RuntimeError", "Exception")))[-900:]
        await update.reply(f"❌ خطا: {str(e)[:200]}\n\n{short}")


# ======================= محافظت گروه و بازی =======================
# هشدار: حذف پیام/اخراج با متدهای API روبیکا انجام می‌شود (rb_call) که اسم و پارامترهایشان حدسی است
# و ربات باید در گروه ادمین با دسترسی حذف پیام و بن عضو باشد. تشخیص نوع پیام (عکس/فایل/فوروارد/...)
# هم به فیلدهای rubpy وابسته است؛ با دستور «تشخیص» (ریپلای روی پیام) می‌شود آن را بررسی کرد.
DATA_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "chatdata.json")
_data = None
LOCKS = {"لینک": "link", "اسپم": "spam", "عکس": "photo", "ویدیو": "video",
         "فایل": "file", "ویس": "voice", "استیکر": "sticker", "فوروارد": "forward"}
LINK_RE = re.compile(
    r"(https?://|www\.|t\.me/|rubika\.ir|@[A-Za-z0-9_]{4,}|"
    r"\b[\w-]+\.(com|ir|org|net|me|io|info|xyz|ly)\b)", re.I)
_DIGITS = str.maketrans("۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩", "01234567890123456789")
_recent: dict = defaultdict(lambda: deque(maxlen=10))
games: dict = {}  # guid گروه -> وضعیت بازی جاری

QUIZ = [
    ("پایتخت ایران کدام شهر است؟", ["تهران"]),
    ("بزرگ‌ترین سیاره‌ی منظومه‌ی شمسی کدام است؟", ["مشتری"]),
    ("حاصل ۷ × ۸ چند است؟", ["56", "پنجاه و شش"]),
    ("پایتخت فرانسه کدام شهر است؟", ["پاریس"]),
    ("سریع‌ترین جانور خشکی کدام است؟", ["یوزپلنگ", "یوز"]),
    ("نماد شیمیایی آب چیست؟", ["h2o"]),
    ("چند قاره در جهان داریم؟", ["7", "هفت"]),
    ("بلندترین قله‌ی جهان چه نام دارد؟", ["اورست"]),
    ("نزدیک‌ترین ستاره به زمین کدام است؟", ["خورشید"]),
    ("حافظ اهل کدام شهر بود؟", ["شیراز"]),
    ("پایتخت ژاپن کدام شهر است؟", ["توکیو", "tokyo"]),
    ("کدام سیاره به «سیاره‌ی سرخ» معروف است؟", ["مریخ"]),
    ("در یک دقیقه چند ثانیه است؟", ["60", "شصت"]),
    ("بزرگ‌ترین اقیانوس جهان کدام است؟", ["اقیانوس آرام", "آرام"]),
    ("شاهنامه را چه کسی سرود؟", ["فردوسی"]),
]
RIDDLES = [
    ("چیست که هرچه از آن بیشتر برداری، بزرگ‌تر می‌شود؟", ["چاله", "گودال"]),
    ("چیست که پا ندارد ولی راه می‌رود؟", ["ساعت"]),
    ("چیست که هرچه بیشتر خشک کند، خودش خیس‌تر می‌شود؟", ["حوله"]),
    ("چه چیزی دندان دارد ولی گاز نمی‌گیرد؟", ["شانه", "اره"]),
    ("کدام ماه‌ها ۲۸ روز دارند؟", ["همه", "همه ماه‌ها"]),
    ("چیست که چشم دارد ولی نمی‌بیند؟", ["سوزن"]),
    ("چیست که اگر اسمش را بگویی، از بین می‌رود؟", ["سکوت"]),
]


def _d() -> dict:
    global _data
    if _data is None:
        try:
            with open(DATA_FILE, encoding="utf-8") as f:
                _data = json.load(f)
        except (FileNotFoundError, json.JSONDecodeError):
            _data = {}
    return _data


def _dsave() -> None:
    tmp = DATA_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(_data, f, ensure_ascii=False)
    os.replace(tmp, DATA_FILE)


def cdata(chat_guid: str) -> dict:
    c = _d().setdefault(chat_guid, {})
    for k in ("locks", "muted", "warns", "scores", "names", "stats", "profile"):
        c.setdefault(k, {})
    return c


def norm_ans(t: str) -> str:
    t = t.lower().translate(_DIGITS).replace("ي", "ی").replace("ك", "ک")
    return re.sub(r"[\s‌\.,،؛:!؟?\-_\"'«»()]+", "", t)


def display_name(update) -> str:
    for n in ("author_title", "author_name", "sender_name", "title"):
        v = getattr(update, n, None)
        if isinstance(v, str) and v:
            return v
    g = sender_guid(update) or "?"
    return "کاربر…" + g[-4:]


async def say(update, text: str):
    """پاسخ به پیام؛ اگر پیام اصلی پاک شده بود، پیام مستقل بفرست"""
    try:
        return await update.reply(text)
    except Exception:
        try:
            r = bot.send_message(update.object_guid, text)
            return await r if inspect.isawaitable(r) else r
        except Exception as e:
            print("say error:", str(e)[:150])


async def delete_msg(update) -> bool:
    try:
        await rb_call("deleteMessages", object_guid=update.object_guid,
                      message_ids=[update.message_id], type="Global")
        return True
    except Exception as e:
        print("delete error:", str(e)[:200])
        return False


def media_kinds(update) -> set:
    """نوع محتوای پیام: photo/video/file/voice/sticker/forward (تشخیص حدسی)"""
    kinds = set()
    fi = getattr(update, "file_inline", None)
    if fi is not None:
        t = fi.get("type") if isinstance(fi, dict) else getattr(fi, "type", "")
        t = str(t or "").lower()
        if "image" in t or "photo" in t:
            kinds.add("photo")
        elif "video" in t or "gif" in t:
            kinds.add("video")
        elif "voice" in t:
            kinds.add("voice")
        else:
            kinds.add("file")
    if getattr(update, "sticker", None):
        kinds.add("sticker")
    if any(getattr(update, n, None) for n in ("forwarded_from", "forwarded_no_link", "forward_from")):
        kinds.add("forward")
    return kinds


async def warn_user(update, c: dict, sender: str, reason: str, name: str | None = None):
    n = c["warns"].get(sender, 0) + 1
    if n >= 3:
        c["warns"][sender] = 0
        c["muted"][sender] = time.time() + 600
        tail = "۳ اخطار شد → ۱۰ دقیقه سکوت 🔇"
    else:
        c["warns"][sender] = n
        tail = f"اخطار {n} از ۳"
    _dsave()
    await say(update, f"⚠️ {name or display_name(update)}: {reason}\n{tail}")


async def protect(update, text: str, sender: str | None) -> bool:
    """True یعنی پیام پاک شد/رد شد و پردازش ادامه نمی‌یابد"""
    if not sender or is_allowed(sender):
        return False  # افراد مجاز و ادمین‌های ربات معاف‌اند
    c = cdata(update.object_guid)
    until = c["muted"].get(sender)
    if until is not None:
        if until == 0 or until > time.time():
            await delete_msg(update)
            return True
        c["muted"].pop(sender, None)
        _dsave()
    L = c["locks"]
    if L.get("link") and text and LINK_RE.search(text):
        await delete_msg(update)
        await warn_user(update, c, sender, "ارسال لینک و آیدی ممنوع است")
        return True
    kinds = media_kinds(update)
    for k in ("photo", "video", "file", "voice", "sticker", "forward"):
        if L.get(k) and k in kinds:
            await delete_msg(update)
            return True
    if L.get("spam"):
        now = time.time()
        q = _recent[(update.object_guid, sender)]
        q.append((now, norm_ans(text)))
        burst = sum(1 for t, _ in q if now - t <= 8)
        same = sum(1 for t, x in q if now - t <= 30 and x and x == q[-1][1])
        if burst >= 6 or same >= 3:
            q.clear()
            await delete_msg(update)
            await warn_user(update, c, sender, "لطفاً پیام تکراری یا پشت‌سرهم نفرستید")
            return True
    return False


async def mod_cmd(update, text: str, sender: str) -> bool:
    """دستورهای مدیریتی گروه (فقط ادمین ربات)"""
    c = cdata(update.object_guid)
    m = re.fullmatch(r"(قفل|بازکردن|باز کردن)\s+(\S+)", text)
    if m and m.group(2) in LOCKS:
        on = m.group(1) == "قفل"
        c["locks"][LOCKS[m.group(2)]] = on
        _dsave()
        await say(update, f"{'🔒' if on else '🔓'} {m.group(2)} {'قفل شد' if on else 'باز شد'}.")
        return True
    if text in ("وضعیت قفل ها", "وضعیت قفل‌ها", "قفل ها"):
        rows = [f"{'🔒' if c['locks'].get(v) else '🔓'} {k}" for k, v in LOCKS.items()]
        await say(update, "وضعیت قفل‌ها:\n" + "\n".join(rows))
        return True

    m = re.fullmatch(r"(سکوت|رفع سکوت|اخراج|اخطار|تشخیص)(?:\s+(\d{1,4}))?", text)
    if not m:
        return False
    cmd, mins = m.group(1), m.group(2)
    try:
        replied = await update.get_reply_message()
    except Exception:
        replied = None
    if replied is None:
        await say(update, "روی پیام همان فرد ریپلای کنید و دستور را بنویسید.")
        return True
    if cmd == "تشخیص":
        names = [n for n in dir(replied) if not n.startswith("_") and
                 any(k in n.lower() for k in ("guid", "type", "file", "forward", "sticker", "author", "title", "text"))]
        await say(update, f"نوع تشخیص‌داده‌شده: {sorted(media_kinds(replied)) or 'متن'}\nفیلدها: {', '.join(names)[:900]}")
        return True
    target = sender_guid(replied)
    if not target:
        await say(update, "فرستنده‌ی آن پیام تشخیص داده نشد.")
        return True
    if is_admin(target):
        await say(update, "روی ادمین ربات نمی‌شود این دستور را زد.")
        return True
    if cmd == "سکوت":
        c["muted"][target] = time.time() + int(mins) * 60 if mins else 0
        _dsave()
        await say(update, f"🔇 سکوت شد ({mins + ' دقیقه' if mins else 'تا اطلاع بعدی'}). پیام‌هایش پاک می‌شود.")
    elif cmd == "رفع سکوت":
        c["muted"].pop(target, None)
        c["warns"].pop(target, None)
        _dsave()
        await say(update, "🔊 سکوت برداشته شد.")
    elif cmd == "اخطار":
        await warn_user(update, c, target, "اخطار از طرف ادمین", name=display_name(replied))
    elif cmd == "اخراج":
        try:
            await rb_call("banGroupMember", group_guid=update.object_guid, member_guid=target, action="Set")
            await say(update, "🚪 اخراج شد.")
        except Exception as e:
            await say(update, f"❌ اخراج ناموفق (ربات باید ادمین با دسترسی بن باشد): {str(e)[:200]}")
    return True


# ---------- بازی‌ها ----------
def add_score(c: dict, guid: str, name: str, pts: int):
    c["scores"][guid] = c["scores"].get(guid, 0) + pts
    c["names"][guid] = name
    _dsave()


async def _timeout_reveal(chat_guid: str, game: dict, secs: int = 60):
    await asyncio.sleep(secs)
    if games.get(chat_guid) is game:
        games.pop(chat_guid, None)
        try:
            r = bot.send_message(chat_guid, f"⏰ وقت تمام شد! جواب: {game['answers'][0]}")
            if inspect.isawaitable(r):
                await r
        except Exception as e:
            print("timeout msg error:", str(e)[:150])


async def game_public(update, text: str, sender: str | None) -> bool:
    """پاسخ‌دادن به بازی جاری و جدول امتیاز؛ برای همه‌ی اعضا"""
    guid = update.object_guid
    c = cdata(guid)
    if text in ("جدول امتیاز", "جدول امتیازات", "امتیازات"):
        top = sorted(c["scores"].items(), key=lambda x: -x[1])[:10]
        if not top:
            await say(update, "هنوز امتیازی ثبت نشده است.")
        else:
            medals = ["🥇", "🥈", "🥉"] + ["🔹"] * 7
            rows = [f"{medals[i]} {c['names'].get(g, g[-4:])}: {s}" for i, (g, s) in enumerate(top)]
            await say(update, "🏆 جدول امتیاز:\n" + "\n".join(rows))
        return True

    g = games.get(guid)
    if not g or not sender or sender == getattr(bot, "guid", None) or not text:
        return False
    name = display_name(update)
    if g["type"] == "guess":
        t = text.translate(_DIGITS).strip()
        if not t.isdigit():
            return False
        n = int(t)
        g["tries"] += 1
        if n == g["secret"]:
            games.pop(guid, None)
            add_score(c, sender, name, 3)
            await say(update, f"🎉 {name} درست حدس زد: {n}\nبعد از {g['tries']} حدس. +۳ امتیاز")
        else:
            await say(update, "⬆️ بزرگ‌تر" if n < g["secret"] else "⬇️ کوچک‌تر")
        return True
    if g["type"] in ("quiz", "riddle"):
        if len(text) > 60:
            return False
        if norm_ans(text) in [norm_ans(a) for a in g["answers"]]:
            games.pop(guid, None)
            add_score(c, sender, name, 2)
            await say(update, f"✅ {name} درست جواب داد: {g['answers'][0]}\n+۲ امتیاز")
            return True
        return False
    if g["type"] == "rps" and text in ("سنگ", "کاغذ", "قیچی"):
        bot_pick = random.choice(["سنگ", "کاغذ", "قیچی"])
        wins = {("سنگ", "قیچی"), ("قیچی", "کاغذ"), ("کاغذ", "سنگ")}
        if text == bot_pick:
            res = "مساوی 🤝"
        elif (text, bot_pick) in wins:
            add_score(c, sender, name, 1)
            res = "تو بردی! +۱ امتیاز 🎉"
        else:
            res = "من بردم 😎"
        await say(update, f"{name}: {text} | ربات: {bot_pick}\n{res}")
        return True
    return False


async def game_start(update, text: str) -> bool:
    """شروع/پایان بازی؛ فقط افراد مجاز"""
    guid = update.object_guid
    if text == "بازی حدس عدد":
        games[guid] = {"type": "guess", "secret": random.randint(1, 100), "tries": 0}
        await say(update, "🔢 یک عدد بین ۱ تا ۱۰۰ انتخاب کردم. حدس بزنید! (فقط عدد بنویسید)")
    elif text in ("بازی کوییز", "بازی کویز"):
        q, ans = random.choice(QUIZ)
        g = games[guid] = {"type": "quiz", "answers": ans}
        await say(update, f"❓ کوییز:\n{q}\n(۶۰ ثانیه وقت دارید)")
        asyncio.create_task(_timeout_reveal(guid, g))
    elif text == "بازی معما":
        q, ans = random.choice(RIDDLES)
        g = games[guid] = {"type": "riddle", "answers": ans}
        await say(update, f"🧩 معما:\n{q}\n(۶۰ ثانیه وقت دارید)")
        asyncio.create_task(_timeout_reveal(guid, g))
    elif text in ("بازی سنگ کاغذ قیچی", "بازی سنگ"):
        games[guid] = {"type": "rps"}
        await say(update, "✊✋✌️ بنویسید: سنگ / کاغذ / قیچی (برای پایان: پایان بازی)")
    elif text == "جواب" and guid in games and "answers" in games[guid]:
        a = games.pop(guid)["answers"][0]
        await say(update, f"جواب: {a}")
    elif text == "پایان بازی":
        games.pop(guid, None)
        await say(update, "بازی تمام شد.")
    else:
        return False
    return True



# ---------- آمار پیام‌ها، لقب و اصل ----------
TEHRAN = timezone(timedelta(hours=3, minutes=30))
_unsaved = 0


def _today() -> str:
    return datetime.now(TEHRAN).strftime("%Y-%m-%d")


def count_message(update, sender: str | None):
    """شمارش پیام هر عضو در هر روز (نگه‌داری ۷۰ روز اخیر)"""
    global _unsaved
    if not sender or sender == getattr(bot, "guid", None):
        return
    c = cdata(update.object_guid)
    days = c["stats"].setdefault(sender, {})
    day = _today()
    days[day] = days.get(day, 0) + 1
    c["names"][sender] = display_name(update)
    c["profile"].setdefault(sender, {}).setdefault("since", datetime.now(TEHRAN).isoformat())
    if len(days) > 80:  # پاک‌سازی روزهای قدیمی
        cutoff = (datetime.now(TEHRAN) - timedelta(days=70)).strftime("%Y-%m-%d")
        for k in [k for k in days if k < cutoff]:
            days.pop(k, None)
    _unsaved += 1
    if _unsaved >= 10:
        _unsaved = 0
        _dsave()


atexit.register(lambda: _data is not None and _dsave())


def _sum_days(days: dict, n: int) -> int:
    start = (datetime.now(TEHRAN) - timedelta(days=n - 1)).strftime("%Y-%m-%d")
    return sum(v for k, v in days.items() if k >= start)


_FA = str.maketrans("0123456789", "۰۱۲۳۴۵۶۷۸۹")
CARD_FOOTER = os.environ.get("CARD_FOOTER", "مدیریت گروه")


def fa(n) -> str:
    return str(n).translate(_FA)


def g2j(gy: int, gm: int, gd: int) -> tuple:
    """تبدیل تاریخ میلادی به شمسی"""
    g_d_m = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
    gy2 = gy + 1 if gm > 2 else gy
    days = (355666 + 365 * gy + (gy2 + 3) // 4 - (gy2 + 99) // 100 + (gy2 + 399) // 400
            + gd + g_d_m[gm - 1])
    jy = -1595 + 33 * (days // 12053)
    days %= 12053
    jy += 4 * (days // 1461)
    days %= 1461
    if days > 365:
        jy += (days - 1) // 365
        days = (days - 1) % 365
    if days < 186:
        jm, jd = 1 + days // 31, 1 + days % 31
    else:
        jm, jd = 7 + (days - 186) // 30, 1 + (days - 186) % 30
    return jy, jm, jd


def _jdate(dt: datetime) -> str:
    jy, jm, jd = g2j(dt.year, dt.month, dt.day)
    return f"{jy}/{jm:02d}/{jd:02d}"


def _bar(frac: float, n: int = 10) -> str:
    k = max(0, min(n, round(frac * n)))
    return "▰" * k + "▱" * (n - k)


def _periods() -> dict:
    """تاریخ شروع بازه‌ها: امروز، هفته (از شنبه)، ماه شمسی جاری، دو ماه شمسی اخیر"""
    now = datetime.now(TEHRAN)
    fmt = lambda d: d.strftime("%Y-%m-%d")
    week_start = now - timedelta(days=(now.weekday() - 5) % 7)
    jm_now = g2j(now.year, now.month, now.day)[1]
    month_start = now
    while g2j(*(month_start - timedelta(days=1)).timetuple()[:3])[1] == jm_now:
        month_start -= timedelta(days=1)
    prev = month_start - timedelta(days=1)
    jm_prev = g2j(prev.year, prev.month, prev.day)[1]
    prev_start = prev
    while g2j(*(prev_start - timedelta(days=1)).timetuple()[:3])[1] == jm_prev:
        prev_start -= timedelta(days=1)
    return {"today": fmt(now), "week": fmt(week_start), "month": fmt(month_start), "two": fmt(prev_start)}


def _since(days: dict, start: str) -> int:
    return sum(v for k, v in days.items() if k >= start)


def rank_of(guid: str) -> str:
    if guid == getattr(bot, "guid", None) or guid in OWNER_ENV:
        return "مالک 👑"
    if guid in _access_load()["admins"]:
        return "ادمین ⚡"
    if guid in _access_load()["users"]:
        return "ویژه ✨"
    return "عضو 🔹"


def stats_card(c: dict, guid: str, name: str) -> str:
    days = c["stats"].get(guid, {})
    prof = c["profile"].get(guid, {})
    P = _periods()
    today, week = days.get(P["today"], 0), _since(days, P["week"])
    month, two = _since(days, P["month"]), _since(days, P["two"])
    best = max([_since(d, P["month"]) for d in c["stats"].values()] + [1])
    warns = c["warns"].get(guid, 0)

    asl = prof.get("asl")
    asl_txt = f"{asl['name']} · {fa(asl['age'])} ساله · {asl['city']}" if asl else "ثبت نشده"
    since = "—"
    if prof.get("since"):
        try:
            dt = datetime.fromisoformat(prof["since"]).astimezone(TEHRAN)
            since = fa(_jdate(dt)) + " — " + fa(dt.strftime("%H:%M"))
        except ValueError:
            pass
    return (
        "┏━━━━━━━━━━━━━━━━━┓\n"
        "      ✦ پرونده‌ی عضو ✦\n"
        "┗━━━━━━━━━━━━━━━━━┛\n"
        f"👤 {name}\n"
        f"🏷 لقب  ‹ {prof.get('nick') or 'ثبت نشده'} ›\n"
        f"🎖 مقام  ‹ {rank_of(guid)} ›\n"
        f"📍 اصل  ‹ {asl_txt} ›\n"
        f"🕰 تاریخ پیوست  ‹ {since} ›\n"
        "━━━━ ✉️ پیام‌ها ━━━━\n"
        f"◈ امروز ‹ {fa(today)} ›\n"
        f"◈ این هفته ‹ {fa(week)} ›\n"
        f"◈ این ماه ‹ {fa(month)} ›\n"
        f"◈ دو ماه اخیر ‹ {fa(two)} ›\n"
        f"⚡ فعالیت ماه  {_bar(month / best)}  {fa(round(100 * month / best))}٪\n"
        "━━━━ 🛡 انضباط ━━━━\n"
        f"◈ اخطار ‹ {fa(warns)} از ۳ ›  {_bar(warns / 3, 3)}\n"
        "┈┈┈┈┈┈┈┈┈┈┈┈┈┈\n"
        f"      ❖ {CARD_FOOTER} ❖"
    )


async def profile_cmd(update, text: str, sender: str | None) -> bool:
    """آمار / ثبت لقب / ثبت اصل (برای همه؛ ادمین با ریپلای می‌تواند برای دیگران ثبت کند)"""
    if not sender:
        return False
    t = text.translate(_DIGITS)
    m_nick = re.fullmatch(r"ثبت لقب\s+(.{1,30})", t)
    m_asl = re.fullmatch(r"ثبت اصل\s+(\S{1,20})\s+(\d{1,3})\s+(.{1,30})", t)
    if text != "آمار" and text != "آمار گروه" and not m_nick and not m_asl:
        return False
    c = cdata(update.object_guid)

    if text == "آمار گروه":
        top = sorted(((g, _sum_days(d, 30)) for g, d in c["stats"].items()), key=lambda x: -x[1])[:10]
        top = [(g, n) for g, n in top if n]
        if not top:
            await say(update, "هنوز آماری ثبت نشده است.")
            return True
        medals = ["🥇", "🥈", "🥉"] + ["🔹"] * 7
        rows = [f"{medals[i]} {c['names'].get(g, g[-4:])}: {n} پیام" for i, (g, n) in enumerate(top)]
        await say(update, "🏆 فعال‌ترین اعضا (۳۰ روز اخیر):\n" + "\n".join(rows))
        return True

    # هدف: خود فرستنده؛ اگر ادمین ریپلای کرده باشد، آن فرد
    target, tname = sender, display_name(update)
    try:
        replied = await update.get_reply_message()
    except Exception:
        replied = None
    if replied is not None:
        rg = sender_guid(replied)
        if rg and rg != sender:
            if text == "آمار" or is_admin(sender):
                target, tname = rg, c["names"].get(rg) or display_name(replied)
            else:
                await say(update, "فقط ادمین می‌تواند برای دیگران ثبت کند.")
                return True

    if text == "آمار":
        _dsave()
        await say(update, stats_card(c, target, tname))
        return True
    prof = c["profile"].setdefault(target, {})
    if m_nick:
        prof["nick"] = m_nick.group(1).strip()
        _dsave()
        await say(update, f"✅ لقب ثبت شد: {prof['nick']}")
        return True
    age = int(m_asl.group(2))
    if not 5 <= age <= 120:
        await say(update, "سن واردشده معتبر نیست.")
        return True
    prof["asl"] = {"name": m_asl.group(1), "age": age, "city": m_asl.group(3).strip()}
    _dsave()
    await say(update, "✅ اصل ثبت شد.")
    return True


@bot.on_message_updates()
async def on_text(update: Updates):
    text = (update.text or "").strip()
    chat = state[update.object_guid]

    # ---- کنترل دسترسی ----
    global _warned_sender
    sender = sender_guid(update)
    if text in ("guid من", "آیدی من"):  # برای معرفی خودتان به مالک؛ بقیه‌ی دستورها قفل است
        return await update.reply(f"guid شما: {sender or 'نامشخص'}")
    if sender is None and not _warned_sender:
        _warned_sender = True
        print("هشدار: فرستنده تشخیص داده نشد. فیلدهای update:",
              [n for n in dir(update) if not n.startswith("_") and "guid" in n.lower()])
    if await protect(update, text, sender):
        return
    count_message(update, sender)
    if await profile_cmd(update, text, sender):
        return
    if await game_public(update, text, sender):
        return
    if not is_allowed(sender):
        return  # بی‌صدا نادیده بگیر
    if await game_start(update, text):
        return

    if is_admin(sender):
        if await mod_cmd(update, text, sender):
            return
        if text in ("افزودن", "ادمین", "افزودن ادمین", "حذف"):
            try:
                replied = await update.get_reply_message()
            except Exception:
                replied = None
            target = sender_guid(replied) if replied else None
            if not target:
                return await update.reply("روی پیام همان فرد ریپلای کنید و این دستور را بنویسید.")
            acc = _access_load()
            if text == "حذف":
                acc["users"] = [g for g in acc["users"] if g != target]
                acc["admins"] = [g for g in acc["admins"] if g != target]
                _access_save(acc)
                return await update.reply("🗑 دسترسی این فرد حذف شد.")
            key = "admins" if text in ("ادمین", "افزودن ادمین") else "users"
            if target not in acc[key]:
                acc[key].append(target)
            _access_save(acc)
            return await update.reply("✅ " + ("ادمین" if key == "admins" else "کاربر مجاز") + " اضافه شد.")
        if text == "لیست مجازها":
            acc = _access_load()
            return await update.reply(f"👑 ادمین‌ها: {len(acc['admins'])}\n👤 کاربران مجاز: {len(acc['users'])}")

    # تنظیم صدا
    m = re.fullmatch(r"تنظیم صدا\s+(\d{1,3})", text)
    if m:
        v = int(m.group(1))
        if not 0 <= v <= 200:
            return await update.reply("عدد صدا باید بین 0 تا 200 باشد.")
        chat["volume"] = v
        return await update.reply(f"🔊 صدا روی {v}% تنظیم شد (برای موزیک‌های بعدی).")

    # تنظیم سرعت
    m = re.fullmatch(r"تنظیم سرعت\s+([0-9]*\.?[0-9]+)", text)
    if m:
        s = float(m.group(1))
        if not 0.5 <= s <= 2:
            return await update.reply("سرعت باید بین 0.5 تا 2 باشد.")
        chat["speed"] = s
        return await update.reply(f"⚡ سرعت روی {s}x تنظیم شد (برای موزیک‌های بعدی).")

    # تشخیص: لیست متدهای مرتبط rubpy
    if text == "متدها":
        try:
            from importlib.metadata import version
            ver = version("rubpy")
        except Exception:
            ver = "?"
        names = [n for n in dir(bot) if not n.startswith("_") and
                 any(k in n.lower() for k in ("send", "file", "download", "upload", "voice", "music"))]
        return await update.reply(f"rubpy {ver}\n" + ", ".join(names)[:1500])

    # کال: حضور در ویس‌چت گروه و پخش داخل آن
    if text == "کال":
        if update.object_guid in calls:
            return await update.reply("ربات الان در کال است.")
        vc = VoiceCall(update.object_guid)
        try:
            await vc.start()
        except Exception as e:
            traceback.print_exc()
            await vc.leave(discard=False)
            return await update.reply(f"❌ کال: {str(e)[:700]}")
        calls[update.object_guid] = vc
        return await update.reply("📞 وارد کال شدم. حالا «پخش آهنگ ...» را بزنید.")

    if text == "پایان کال":
        vc = calls.pop(update.object_guid, None)
        if not vc:
            return await update.reply("ربات در کال نیست.")
        await vc.leave()
        return await update.reply("📴 کال بسته شد.")

    if text == "وضعیت کال":
        vc = calls.get(update.object_guid)
        if not vc:
            return await update.reply("ربات در کال نیست.")
        return await update.reply(vc.status()[:1800])

    if text == "توقف" and update.object_guid in calls:
        calls[update.object_guid].stop_track()
        return await update.reply("⏹ پخش متوقف شد.")

    # پلی لیست
    if re.fullmatch(r"پلی\s?لیست", text):
        if not chat["playlist"]:
            return await update.reply("پلی‌لیست خالی است.")
        lines = [f"{i}- {e['title']}" for i, e in enumerate(chat["playlist"], 1)]
        return await update.reply("📜 پلی‌لیست:\n" + "\n".join(lines))

    # پخش
    if text == "پخش":
        return await play(update, chat, None)

    m = re.fullmatch(r"پخش\s+(\d{1,2})", text)  # پخش 4
    if m:
        i = int(m.group(1))
        pl = list(chat["playlist"])
        if not 1 <= i <= len(pl):
            return await update.reply("این شماره در پلی‌لیست نیست.")
        entry = pl[i - 1]
        if not os.path.exists(entry["src"]):
            return await update.reply("فایل این موزیک دیگر در دسترس نیست.")
        final = await apply_effects(entry["src"], chat["volume"], chat["speed"])
        return await send_music(update, final, entry["title"])

    m = re.fullmatch(r"پخش\s+(https?://\S+)", text)  # پخش لینک
    if m:
        return await play(update, chat, m.group(1))

    m = re.fullmatch(r"پخش\s+آهنگ\s+(.+)", text, flags=re.S)  # پخش آهنگ ...
    if m:
        return await play(update, chat, m.group(1).strip())




# ======================= اجرا =======================
def run_panel():
    # فقط روی همین دستگاه در دسترس است
    app.run(host="127.0.0.1", port=int(os.environ.get("PANEL_PORT", "8080")), use_reloader=False)


if __name__ == "__main__":
    threading.Thread(target=run_panel, daemon=True).start()
    print("پنل: http://127.0.0.1:%s" % os.environ.get("PANEL_PORT", "8080"))
    bot.run()
