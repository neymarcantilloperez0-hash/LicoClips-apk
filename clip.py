#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Lico Clips - saca los mejores momentos de un VOD (Kick, Twitch, YouTube...) y los deja
listos para TikTok / Facebook Reels. Flask + FFmpeg + yt-dlp. Pensado para Termux.

Instalar (una sola vez):
    pkg update && pkg install python ffmpeg
    pip install flask yt-dlp
    (opcional para links de Kick)  pip install "yt-dlp[default,curl-cffi]"

Usar:
    python clip.py          ->  abre http://localhost:5000 en Chrome
    termux-wake-lock        ->  (recomendado) evita que Android duerma la app; necesario para publicaciones programadas

Claves opcionales (se pegan en la pestaña Ajustes):
    Anthropic -> detecta tu camara con IA, clasifica momentos y escribe titulos/textos
    OpenAI    -> transcribe (categorias por contenido y subtitulos automaticos)
"""
import base64
import copy
import hashlib
import json
import math
import os
import re
import shutil
import statistics
import struct
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import unicodedata
import uuid
from collections import deque
from datetime import datetime
from pathlib import Path

from flask import Flask, Response, abort, jsonify, redirect, request, send_file

BASE = Path(__file__).resolve().parent
DATA = Path(os.environ.get("CH_DATA") or (BASE / "data"))
JOBS_DIR = DATA / "jobs"
ASSETS_DIR = DATA / "assets"
CONFIG_FILE = DATA / "config.json"
QUEUE_FILE = DATA / "queue.json"
for _d in (JOBS_DIR, ASSETS_DIR):
    _d.mkdir(parents=True, exist_ok=True)

# ffmpeg / yt-dlp locales (sin Termux): carpeta bin/ o junto a clip.py
_LOCAL_BINS = [BASE / "bin", BASE] + sorted(BASE.glob("ffmpeg*/bin"))
for _b in _LOCAL_BINS:
    if _b.is_dir():
        os.environ["PATH"] = str(_b) + os.pathsep + os.environ.get("PATH", "")

PORT = int(os.environ.get("PORT", 5000))
MODEL = os.environ.get("CLAUDE_MODEL", "claude-sonnet-5-5")
STEP = 0.5  # segundos por muestra de audio
KEEP_DAYS = 30

# APIs de redes (se pueden cambiar por variables de entorno, sirve para pruebas)
FB_GRAPH = os.environ.get("CH_FB_GRAPH", "https://graph.facebook.com/v25.0")
FB_RUPLOAD = os.environ.get("CH_FB_RUPLOAD", "https://rupload.facebook.com/video-upload/v25.0")
FB_DIALOG = os.environ.get("CH_FB_DIALOG", "https://www.facebook.com/v25.0/dialog/oauth")
TT_BASE = os.environ.get("CH_TT_BASE", "https://open.tiktokapis.com")
TT_AUTH = os.environ.get("CH_TT_AUTH", "https://www.tiktok.com/v2/auth/authorize/")
TT_CHUNK = int(os.environ.get("CH_TT_CHUNK", 64 * 1024 * 1024))  # 5 MB .. 64 MB

JOBS = {}
JOBS_LOCK = threading.RLock()
CFG_LOCK = threading.RLock()


# ---------------------------------------------------------------- configuracion
def load_config():
    try:
        return json.loads(CONFIG_FILE.read_text())
    except Exception:
        return {}


def save_config(cfg):
    with CFG_LOCK:
        tmp = CONFIG_FILE.with_suffix(".tmp")
        tmp.write_text(json.dumps(cfg))
        try:
            os.chmod(tmp, 0o600)
        except Exception:
            pass
        os.replace(tmp, CONFIG_FILE)


def cfg_update(fn):
    with CFG_LOCK:
        cfg = load_config()
        fn(cfg)
        save_config(cfg)
        return cfg


def get_key(name):
    return os.environ.get(name.upper()) or load_config().get(name.lower()) or ""


def account(name):
    return dict((load_config().get("accounts") or {}).get(name) or {})


def set_account(name, data):
    def fn(cfg):
        cfg.setdefault("accounts", {})[name] = data
    cfg_update(fn)


# ---------------------------------------------------------------- utilidades
def hms(sec):
    sec = max(0, int(round(sec)))
    return f"{sec // 3600}:{sec % 3600 // 60:02d}:{sec % 60:02d}"


def parse_time(s):
    s = (s or "").strip()
    if not s:
        return None
    try:
        parts = [float(x) for x in s.replace(",", ".").split(":")]
    except ValueError:
        return None
    t = 0.0
    for p in parts:
        t = t * 60 + p
    return t


def even(n):
    return max(2, int(round(n / 2.0)) * 2)


def clamp(v, lo, hi, default):
    try:
        v = float(v)
        if v != v:
            return default
        return min(max(v, lo), hi)
    except Exception:
        return default


def now():
    return time.time()


FONT_CANDIDATES = [
    os.environ.get("FONT_FILE", ""),
    "/data/data/com.termux/files/usr/share/fonts/TTF/DejaVuSans-Bold.ttf",
    "/data/data/com.termux/files/usr/share/fonts/dejavu/DejaVuSans-Bold.ttf",
    "/system/fonts/Roboto-Bold.ttf", "/system/fonts/Roboto-Regular.ttf",
    "/system/fonts/NotoSans-Bold.ttf", "/system/fonts/DroidSans-Bold.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf",
]
_FONT_CACHE = {}


def find_font():
    if "p" in _FONT_CACHE:
        return _FONT_CACHE["p"]
    found = ""
    for p in FONT_CANDIDATES:
        if p and os.path.exists(p):
            found = p
            break
    if not found:
        for d in ("/system/fonts", "/data/data/com.termux/files/usr/share/fonts"):
            if os.path.isdir(d):
                for root, _, files in os.walk(d):
                    for f in files:
                        if f.lower().endswith((".ttf", ".otf")):
                            found = os.path.join(root, f)
                            break
                    if found:
                        break
            if found:
                break
    _FONT_CACHE["p"] = found
    return found


def ttf_family(path):
    """Nombre de familia de una fuente .ttf/.otf (lo necesitan los subtitulos .ass)."""
    try:
        data = Path(path).read_bytes()
        off = 0
        if data[:4] == b"ttcf":
            off = struct.unpack(">I", data[12:16])[0]
        n = struct.unpack(">H", data[off + 4:off + 6])[0]
        for i in range(n):
            rec = data[off + 12 + 16 * i: off + 28 + 16 * i]
            if rec[:4] == b"name":
                o, ln = struct.unpack(">II", rec[8:16])
                tbl = data[o:o + ln]
                count, soff = struct.unpack(">HH", tbl[2:6])
                best = None
                for k in range(count):
                    pid, _eid, _lid, nid, l2, o2 = struct.unpack(">HHHHHH", tbl[6 + 12 * k: 18 + 12 * k])
                    if nid == 1:
                        raw = tbl[soff + o2: soff + o2 + l2]
                        s = raw.decode("utf-16-be" if pid in (0, 3) else "latin-1", "ignore")
                        if s:
                            best = s
                            if pid == 3:
                                break
                return best
    except Exception:
        pass
    return None


def ytdlp_cmd():
    env = os.environ.get("CLIP_YTDLP")
    if env:
        return env.split()
    for _b in (BASE / "bin", BASE):
        for _n in ("yt-dlp.exe", "yt-dlp"):
            _p = _b / _n
            if _p.is_file():
                return [str(_p)] if _n.endswith(".exe") else [sys.executable, str(_p)]
    exe = shutil.which("yt-dlp")
    if exe:
        return [exe]
    try:
        import yt_dlp  # noqa: F401
        return [sys.executable, "-m", "yt_dlp"]
    except ImportError:
        return None


def parse_rate(s):
    try:
        a, b = str(s).split("/")
        return float(a) / float(b) if float(b) else 0
    except Exception:
        try:
            return float(s)
        except Exception:
            return 0


def probe(path):
    r = subprocess.run(["ffprobe", "-v", "error", "-print_format", "json", "-show_streams", "-show_format", str(path)],
                       capture_output=True, text=True)
    if r.returncode:
        raise RuntimeError("No pude leer el video: " + r.stderr[-300:])
    j = json.loads(r.stdout)
    v = next((s for s in j.get("streams", []) if s.get("codec_type") == "video"), None)
    if not v:
        raise RuntimeError("El archivo no tiene video")
    w, h = int(v["width"]), int(v["height"])
    rot = 0
    try:
        rot = int(float(v.get("tags", {}).get("rotate", 0)))
    except Exception:
        pass
    for sd in v.get("side_data_list", []) or []:
        if "rotation" in sd:
            rot = int(float(sd["rotation"]))
    if abs(rot) % 180 == 90:
        w, h = h, w
    a = next((s for s in j["streams"] if s.get("codec_type") == "audio"), None)
    return {"width": w, "height": h, "vcodec": v.get("codec_name"), "has_audio": a is not None,
            "fps": parse_rate(v.get("avg_frame_rate")) or parse_rate(v.get("r_frame_rate")) or 30.0,
            "duration": float(j.get("format", {}).get("duration") or v.get("duration") or 0),
            "size": int(j.get("format", {}).get("size") or 0)}


class Cancelled(Exception):
    pass


def setp(job, pct, stage=None):
    job["progress"] = max(job.get("progress", 0), min(100, int(pct)))
    if stage:
        job["stage"] = stage
        job["log"].append(stage)


def run_ffmpeg(job, args, label, total=None, p0=0, p1=100):
    cmd = ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error", "-nostdin", "-progress", "pipe:1", "-nostats"] + args
    errpath = job["dir"] / f"err_{label}.log"
    with open(errpath, "w+") as errf:
        proc = subprocess.Popen(cmd, cwd=job["dir"], stdout=subprocess.PIPE, stderr=errf, text=True)
        job["proc"] = proc
        for line in proc.stdout:
            if job.get("cancel"):
                proc.terminate()
                break
            if total and (line.startswith("out_time_us=") or line.startswith("out_time_ms=")):
                try:
                    setp(job, p0 + (p1 - p0) * min(1.0, int(line.split("=")[1]) / 1e6 / total))
                except Exception:
                    pass
        proc.wait()
        job["proc"] = None
        if job.get("cancel"):
            raise Cancelled()
        if proc.returncode != 0:
            errf.seek(0)
            raise RuntimeError(f"FFmpeg ({label}) falló: " + errf.read()[-600:])


def multipart(fields, files):
    boundary = "----ch" + uuid.uuid4().hex
    body = b""
    for k, v in fields:
        body += f'--{boundary}\r\nContent-Disposition: form-data; name="{k}"\r\n\r\n{v}\r\n'.encode()
    for k, fname, data, ctype in files:
        body += (f'--{boundary}\r\nContent-Disposition: form-data; name="{k}"; filename="{fname}"\r\n'
                 f'Content-Type: {ctype}\r\n\r\n').encode() + data + b"\r\n"
    body += f"--{boundary}--\r\n".encode()
    return body, f"multipart/form-data; boundary={boundary}"


def http_json(method, url, headers=None, json_body=None, form=None, timeout=60):
    """Llamada HTTP simple -> (status, objeto_json). No lanza error por 4xx/5xx."""
    h = dict(headers or {})
    data = None
    if json_body is not None:
        data = json.dumps(json_body).encode()
        h.setdefault("Content-Type", "application/json; charset=UTF-8")
    elif form is not None:
        data = urllib.parse.urlencode(form).encode()
        h.setdefault("Content-Type", "application/x-www-form-urlencoded")
    req = urllib.request.Request(url, data=data, headers=h, method=method)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            status, raw = r.status, r.read().decode(errors="ignore")
    except urllib.error.HTTPError as e:
        status, raw = e.code, e.read().decode(errors="ignore")
    except urllib.error.URLError as e:
        raise RuntimeError(f"No pude conectar con {urllib.parse.urlparse(url).netloc}: {e.reason}")
    try:
        return status, json.loads(raw) if raw.strip() else {}
    except ValueError:
        return status, {"raw": raw[:300]}


def fmt_when(ts):
    return datetime.fromtimestamp(ts).strftime("%d/%m %H:%M")


# ---------------------------------------------------------------- IA (opcional)
def call_claude(system, content, max_tokens=3000, timeout=120):
    key = get_key("anthropic_key")
    if not key:
        raise RuntimeError("falta la clave de Anthropic")
    body = json.dumps({"model": MODEL, "max_tokens": max_tokens, "system": system,
                       "messages": [{"role": "user", "content": content}]}).encode()
    req = urllib.request.Request(os.environ.get("CH_ANTHROPIC_URL", "https://api.anthropic.com/v1/messages"), data=body,
                                 headers={"x-api-key": key, "anthropic-version": "2023-06-01",
                                          "content-type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            data = json.load(r)
    except urllib.error.HTTPError as e:
        raise RuntimeError(f"Anthropic {e.code}: {e.read().decode(errors='ignore')[:200]}")
    return "".join(b.get("text", "") for b in data.get("content", []) if b.get("type") == "text")


def extract_json(text, kind="{"):
    end = "}" if kind == "{" else "]"
    a, b = text.find(kind), text.rfind(end)
    return json.loads(text[a:b + 1])


def img_block(path):
    return {"type": "image", "source": {"type": "base64", "media_type": "image/jpeg",
                                         "data": base64.b64encode(Path(path).read_bytes()).decode()}}


def whisper(audio_path, verbose=False):
    key = get_key("openai_key")
    if not key:
        raise RuntimeError("falta la clave de OpenAI")
    fields = [("model", "whisper-1"), ("response_format", "verbose_json" if verbose else "text")]
    if verbose:
        fields += [("timestamp_granularities[]", "word"), ("timestamp_granularities[]", "segment")]
    body, ctype = multipart(fields, [("file", "a.mp3", Path(audio_path).read_bytes(), "audio/mpeg")])
    req = urllib.request.Request(os.environ.get("CH_OPENAI_URL", "https://api.openai.com/v1/audio/transcriptions"),
                                 data=body, headers={"Authorization": f"Bearer {key}", "Content-Type": ctype})
    try:
        with urllib.request.urlopen(req, timeout=180) as r:
            raw = r.read().decode()
    except urllib.error.HTTPError as e:
        raise RuntimeError(f"OpenAI {e.code}: {e.read().decode(errors='ignore')[:150]}")
    return json.loads(raw) if verbose else raw.strip()


def cut_audio(job, src, start, dur, out):
    run_ffmpeg(job, ["-ss", f"{start:.2f}", "-t", f"{dur:.2f}", "-i", src, "-vn", "-ac", "1", "-ar", "16000",
                     "-b:a", "48k", out], "aud")


# palabras que delatan el tipo de momento (se usan cuando hay transcripcion)
KEYWORDS = {
    "risas": ["jaja", "jeje", "risa", "me muero", "qué risa", "que risa", "lol", "lmao", "xd", "me meo"],
    "terror": ["ay no", "qué fue eso", "que fue eso", "qué es eso", "miedo", "susto", "grito", "dios mío", "dios mio",
               "no no no", "ayuda", "socorro", "me asusté", "me asuste"],
    "polemica": ["mentira", "mentiroso", "estás loco", "estas loco", "cállate", "callate", "qué te pasa", "que te pasa",
                 "no me jodas", "racista", "trampa", "tramposo", "hacker", "reportar", "pelea", "discusión", "discusion",
                 "funar", "cancelado", "denuncia", "quejarme"],
    "epico": ["increíble", "increible", "qué locura", "que locura", "gg", "vamos", "let's go", "clutch", "no puede ser",
              "ganamos", "victoria", "pentakill", "ace"],
    "fail": ["qué fail", "que fail", "me caí", "me cai", "la cagué", "la cague", "la regué", "la regue", "lag",
             "se me cayó", "se me cayo", "perdí", "perdi"],
}


def keyword_scan(text):
    """-> (categoria_o_None, bonus 0..1.5)."""
    low = (text or "").lower()
    if not low.strip():
        return None, 0.0
    best, best_hits, total = None, 0, 0
    for cat, words in KEYWORDS.items():
        hits = sum(low.count(w) for w in words)
        total += hits
        if hits > best_hits:
            best, best_hits = cat, hits
    return best, min(1.5, 0.5 * total)


CLASSIFY_PROMPT = """You help a streamer clip highlights from a livestream VOD. For each candidate (loud audio moment) you get
frames from the clip, audio stats and sometimes the transcript. Return ONLY a JSON array, one object per candidate:
{"i": <int>, "category": "risas"|"terror"|"polemica"|"epico"|"fail"|"otro", "title": <catchy Spanish title, max 60 chars, no hashtags>,
 "score": <1-10 how good as a short-form clip>, "reason": <one short Spanish sentence>}
Judge by what you SEE and READ. If frames/transcript show nothing interesting, use "otro" and a low score. Do not invent events."""

FACECAM_PROMPT = """This is a frame from a livestream. Find the streamer's FACE-CAM: the small rectangle with the streamer's webcam
(a real person's face / room), usually overlaid on a corner of the game. Do NOT confuse it with game characters or UI.
Return ONLY JSON: {"found": true|false, "x": <left 0-1>, "y": <top 0-1>, "w": <width 0-1>, "h": <height 0-1>}
relative to the whole image (origin top-left). Draw the box tightly around the webcam image, without overlay borders."""

CAPTION_PROMPT = """You write social media captions for short vertical clips from a livestream (TikTok / Facebook Reels).
For each clip you get a title, a category and sometimes a transcript. Return ONLY a JSON array, one object per clip:
{"i": <int>, "caption": <Spanish caption, max 120 chars, punchy, can use 1-2 emojis, NO hashtags>,
 "hashtags": [<4 to 6 relevant lowercase hashtags without the # sign>]}
Do not invent facts that are not in the title/transcript."""


# ---------------------------------------------------------------- trabajos (guardado en disco)
SAVE_LOCK = threading.Lock()
SKIP_KEYS = {"dir", "proc", "cancel"}


def _clean(d):
    return {k: v for k, v in d.items() if k not in SKIP_KEYS}


def save_job(job):
    for attempt in range(4):
        try:
            d = _clean(job)
            d["exports"] = [_clean(e) for e in list(job.get("exports", []))]
            d["clips"] = [dict(c) for c in list(job.get("clips", []))]
            raw = json.dumps(d, default=str)
            break
        except RuntimeError:  # otro hilo estaba cambiando el dict
            time.sleep(0.05)
    else:
        return
    with SAVE_LOCK:
        if not job["dir"].exists():  # el trabajo se borró mientras se guardaba
            return
        try:
            tmp = job["dir"] / "job.json.tmp"
            tmp.write_text(raw, encoding="utf-8")
            os.replace(tmp, job["dir"] / "job.json")
        except FileNotFoundError:
            pass


def new_job(params, label, settings, auto):
    jid = uuid.uuid4().hex[:12]
    jd = JOBS_DIR / jid
    jd.mkdir(parents=True)
    job = {"id": jid, "dir": jd, "created": now(), "label": label, "params": params, "status": "queued", "progress": 0,
           "stage": "En cola…", "log": [], "clips": [], "facecam": None, "facecam_src": "", "error": None,
           "cancel": False, "proc": None, "exports": [], "next_export": 0, "base_offset": 0, "meta": None, "low": None,
           "has_audio": True, "ai_used": False, "orig": params.get("file_name"), "orig_info": None,
           "settings": settings, "auto": bool(auto), "auto_pending": False}
    with JOBS_LOCK:
        JOBS[jid] = job
    return job


def load_jobs():
    n = 0
    for p in sorted(JOBS_DIR.glob("*/job.json")):
        try:
            job = json.loads(p.read_text(encoding="utf-8"))
        except Exception:
            continue
        job["dir"] = p.parent
        job["proc"], job["cancel"] = None, False
        if job.get("status") in ("queued", "running"):
            job["status"], job["error"] = "error", "Se cerró la app mientras analizaba. Vuelve a lanzar el análisis."
        for e in job.get("exports", []):
            e["dir"], e["proc"], e["cancel"] = job["dir"], None, False
            if e.get("status") in ("queued", "running"):
                e["status"], e["error"] = "error", "Se cerró la app mientras creaba este clip. Pulsa Rehacer."
        job.setdefault("next_export", max([e["n"] for e in job.get("exports", [])] + [-1]) + 1)
        job.setdefault("settings", {})
        job.setdefault("facecam_src", "")
        job.setdefault("auto_pending", False)
        with JOBS_LOCK:
            JOBS[job["id"]] = job
        n += 1
    return n


def cleanup_old_jobs():
    cutoff = now() - KEEP_DAYS * 86400
    keep = {t["job"] for t in QUEUE if t["status"] in ("pending", "running")}
    for jid, job in list(JOBS.items()):
        if job["created"] < cutoff and jid not in keep and job["status"] != "running":
            delete_job(jid)


def delete_job(jid):
    with JOBS_LOCK:
        job = JOBS.pop(jid, None)
    if job:
        job["cancel"] = True
        shutil.rmtree(job["dir"], ignore_errors=True)


# ---------------------------------------------------------------- descarga
def dl_extra(url):
    """Kick (y sus .m3u8) piden un 'referer' de kick.com."""
    return ["--referer", "https://kick.com/"] if ("kick.com" in url or "m3u8" in url) else []


def friendly_dl_error(tail):
    txt = "\n".join(tail)
    low = txt.lower()
    if "impersonat" in low and any(k in low for k in ("404", "403", "not found", "forbidden")):
        return ("Kick protege su API y yt-dlp necesita 'curl-cffi' para entrar (sin eso responde 404 o 403). "
                "En Termux prueba: pip install \"yt-dlp[default,curl-cffi]\". "
                "Si no se deja instalar en tu celular, no hay forma de bajar ese VOD por link: sube el video directamente "
                "(o grábalo con la grabadora de pantalla mientras lo ves).")
    if "subscriber" in low:
        return ("Ese VOD es solo para suscriptores, así que Kick no deja descargarlo con un link. "
                "Descarga el video por otro lado y súbelo aquí desde tu celular.")
    if "404" in low or "not found" in low:
        return ("El sitio dice que ese VOD no existe (error 404). Casi siempre: 1) ya expiró o lo borraron (Kick guarda "
                "los VODs 7 días, o hasta 30 si el canal está verificado), 2) es privado, o 3) yt-dlp está desactualizado "
                "(pip install -U yt-dlp). Ábrelo en Chrome: si ahí tampoco se ve, ya no está disponible.")
    if any(k in low for k in ("403", "cloudflare", "impersonat", "captcha", "forbidden")):
        return ("La página bloqueó la descarga automática (pasa seguido con Kick). "
                "Prueba subiendo el video directamente o pegando un enlace .m3u8. Detalle: " + (tail[-1][:200] if tail else ""))
    if "unsupported url" in low:
        return "Ese enlace no es compatible. Usa el enlace del VOD (video guardado), no el del canal en vivo."
    return "No pude descargar el VOD: " + (tail[-1][:250] if tail else "error desconocido")


CAT_LABEL = {"risas": "Risas", "terror": "Terror", "polemica": "Polémica", "epico": "Momento épico", "fail": "Fail",
             "susto": "Susto", "hype": "Hype", "fuerte": "Momento fuerte", "otro": "Momento"}


KICK_ID_RE = re.compile(r"([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})", re.I)


def _find_m3u8(obj):
    """Busca recursivamente el primer texto que parezca un enlace .m3u8."""
    if isinstance(obj, str):
        return obj if (obj.startswith("http") and ".m3u8" in obj) else ""
    if isinstance(obj, dict):
        for k in ("source", "vod", "playback_url", "url"):
            if k in obj:
                r = _find_m3u8(obj[k])
                if r:
                    return r
        for v in obj.values():
            r = _find_m3u8(v)
            if r:
                return r
    if isinstance(obj, list):
        for v in obj:
            r = _find_m3u8(v)
            if r:
                return r
    return ""


def kick_vod_m3u8(url):
    """Metodo directo para VODs de Kick (Kick quito su API vieja /api/v1/video/ y yt-dlp aun no la actualiza).
    Prueba 1) la lista de videos del canal, 2) la API movil. Devuelve (m3u8 o None, motivo del fallo)."""
    m = KICK_ID_RE.search(url or "")
    if not m:
        return None, "no encontré el ID del video en el link (debe tener algo como xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx)"
    vid = m.group(1).lower()
    cm = re.search(r"kick\.com/([A-Za-z0-9_.-]+)/videos/", url)
    slug = cm.group(1) if cm else ""
    try:
        from curl_cffi import requests as cr
    except Exception as e:
        return None, f"curl_cffi no se pudo cargar ({str(e)[:80]})"
    why = []
    hdr = {"Accept": "application/json", "Referer": "https://kick.com/"}

    # 1) lista de videos del canal (el link trae el nombre del canal)
    if slug:
        api = f"https://kick.com/api/v2/channels/{slug}/videos"
        for imp in ("chrome", "chrome120"):
            try:
                r = cr.get(api, impersonate=imp, timeout=30, headers=hdr)
            except Exception as e:
                why.append(f"lista del canal ({imp}): {str(e)[:70]}")
                continue
            if r.status_code != 200:
                why.append(f"lista del canal → HTTP {r.status_code}")
                break
            try:
                data = r.json()
            except Exception:
                why.append("lista del canal: no es JSON")
                break
            items = data if isinstance(data, list) else (data.get("data") or data.get("videos") or [])
            for it in items:
                if vid in json.dumps(it).lower():
                    src = _find_m3u8(it)
                    if src:
                        return src, ""
                    why.append("el video salió en la lista pero sin enlace (¿solo suscriptores?)")
                    break
            else:
                why.append("el video no aparece en la lista del canal (solo trae los más recientes)")
            break

    # 2) API movil de Kick (la misma que usa su app)
    payload = {
        "video_player": {"player": {"player_name": "android_ivs", "player_version": "android_40.26.0",
                                     "player_software": "IVS Player", "player_software_version": "1.52.0"},
                         "mux_sdk": {"sdk_available": True, "mux_sdk_version": "8.9.2"},
                         "datazoom_sdk": {"sdk_available": False, "datazoom_sdk_version": ""},
                         "google_ads_sdk": {"sdk_available": False, "google_ads_sdk_version": ""}},
        "video_session": {"page_type": "UNKNOWN", "player_remote_played": False,
                          "viewer_connection_type": "WIFI", "enable_sampling": True},
        "user_session": {"player_device_id": uuid.uuid4().hex[:16], "player_resettable_id": str(uuid.uuid4()),
                         "player_resettable_consent_type": "idfa"},
    }
    api = f"https://mobile.kick.com/api/v1/stream/{vid}/playback"
    for imp in ("chrome", None):
        try:
            kw = {"impersonate": imp} if imp else {}
            r = cr.post(api, json=payload, timeout=30, headers=hdr, **kw)
        except Exception as e:
            why.append(f"API móvil: {str(e)[:70]}")
            continue
        if r.status_code == 200:
            try:
                src = _find_m3u8((r.json().get("playback_url") or {}).get("vod") or r.json())
            except Exception:
                src = ""
            if src:
                return src, ""
            why.append("API móvil respondió sin enlace del VOD")
            break
        why.append(f"API móvil → HTTP {r.status_code}")
    return None, "; ".join(why) or "sin respuesta"


def is_hls(url):
    return ".m3u8" in (url or "").lower().split("?")[0]


def hls_headers(url):
    return ["-headers", "Referer: https://kick.com/\r\n"] if "kick.com" in url else []


def hls_lowest_map(url):
    """En un .m3u8 maestro, elige la calidad mas liviana (menos bitrate)."""
    try:
        r = subprocess.run(["ffprobe", "-v", "error", "-print_format", "json", "-show_programs"] + hls_headers(url) + [url],
                           capture_output=True, text=True, timeout=60)
        progs = json.loads(r.stdout).get("programs", [])
        best = None
        for pg in progs:
            br = int((pg.get("tags") or {}).get("variant_bitrate") or 0)
            if br and (best is None or br < best[0]):
                best = (br, pg.get("program_id"))
        if best and len(progs) > 1:
            return ["-map", f"0:p:{best[1]}:v:0", "-map", f"0:p:{best[1]}:a:0?"]
    except Exception:
        pass
    return []


def download_low_hls(job):
    p = job["params"]
    url = p["url"]
    a, b = p["t_from"], p["t_to"]
    job["base_offset"] = a or 0
    args = hls_headers(url)
    if a:
        args += ["-ss", f"{a:.2f}"]
    if b:
        args += ["-t", f"{max(10.0, b - (a or 0)):.2f}"]
    total = None
    try:
        total = probe(url)["duration"] if not b else (b - (a or 0))
        if a and not b:
            total -= a
    except Exception:
        pass
    args += ["-i", url] + hls_lowest_map(url) + ["-c", "copy", "-bsf:a", "aac_adtstoasc", "-movflags", "+faststart", "low.mp4"]
    job["stage"] = "Descargando el VOD (enlace .m3u8)…"
    try:
        run_ffmpeg(job, args, "hls", total=total, p0=3, p1=30)
    except RuntimeError:
        # algunos streams no aceptan copiar: lo recodifico liviano
        args2 = [x for x in args if x not in ("-bsf:a", "aac_adtstoasc")]
        i = args2.index("-c")
        args2[i:i + 2] = ["-c:v", "libx264", "-preset", "ultrafast", "-crf", "34", "-vf", "scale=-2:360", "-c:a", "aac", "-b:a", "48k"]
        run_ffmpeg(job, args2, "hls2", total=total, p0=3, p1=30)
    return "low.mp4"


def download_low(job):
    p = job["params"]
    if is_hls(p["url"]):
        return download_low_hls(job)
    cmd = ytdlp_cmd()
    if not cmd:
        if "kick.com" in p["url"]:
            src, why = kick_vod_m3u8(p["url"])
            if src:
                p["url"] = src
                return download_low_hls(job)
        raise RuntimeError("Falta yt-dlp. En Termux: pip install yt-dlp")
    args = cmd + ["--no-playlist", "--newline", "--no-warnings", "--concurrent-fragments", "4",
                  "-f", "b[height<=360]/worst/best", "--merge-output-format", "mp4", "-o", "low.%(ext)s"]
    a, b = p["t_from"], p["t_to"]
    if a is not None or b is not None:
        args += ["--download-sections", f"*{a or 0}-{b if b else 'inf'}"]
    job["base_offset"] = a or 0
    args += dl_extra(p["url"])
    args.append(p["url"])
    proc = subprocess.Popen(args, cwd=job["dir"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    job["proc"] = proc
    tail = deque(maxlen=12)
    for line in proc.stdout:
        tail.append(line.rstrip())
        if job.get("cancel"):
            proc.terminate()
            break
        m = re.search(r"\[download\]\s+([0-9.]+)%", line)
        if m:
            pct = float(m.group(1))
            job["stage"] = f"Descargando el VOD en baja calidad… {pct:.0f}%"
            setp(job, 3 + 27 * pct / 100)
    proc.wait()
    job["proc"] = None
    if job.get("cancel"):
        raise Cancelled()
    files = [f for f in job["dir"].glob("low.*") if f.suffix not in (".part", ".ytdl")]
    if proc.returncode != 0 or not files:
        msg = friendly_dl_error(list(tail))
        if "kick.com" in p["url"]:
            job["stage"] = "yt-dlp no pudo con Kick; pruebo el método directo…"
            src, why = kick_vod_m3u8(p["url"])
            if src:
                job["log"].append("yt-dlp falló con Kick; usé el método directo de Kick.")
                p["url"] = src
                return download_low_hls(job)
            msg += f" | Método directo de Kick: {why}. | yt-dlp dijo: {(tail[-1] if tail else '')[:200]}"
        raise RuntimeError(msg)
    return files[0].name


def make_playable(job, name):
    """Deja el archivo en un formato que Chrome reproduzca y permita saltar."""
    path = job["dir"] / name
    info = probe(path)
    ok_ext = path.suffix.lower() in (".mp4", ".m4v", ".mov", ".webm")
    ok_codec = info["vcodec"] in ("h264", "vp8", "vp9", "av1", "hevc")
    if ok_ext and ok_codec:
        return name, info
    if info["duration"] > 1800:
        # Directos largos: convertir tarda horas. FFmpeg analiza el original tal cual; solo se pierde la vista previa del navegador.
        job["log"].append("Video largo en formato que Chrome no reproduce: lo analizo directo, sin vista previa.")
        return name, info
    setp(job, 30, "Convirtiendo el video a un formato compatible…")
    out = "low_play.mp4"
    run_ffmpeg(job, ["-i", name, "-vf", "scale=-2:480", "-c:v", "libx264", "-preset", "ultrafast", "-crf", "30",
                     "-c:a", "aac", "-b:a", "64k", "-movflags", "+faststart", out], "conv",
               total=info["duration"], p0=30, p1=36)
    return out, probe(job["dir"] / out)


# ---------------------------------------------------------------- deteccion de momentos
def read_series(path):
    vals = []
    try:
        for line in open(path, errors="ignore"):
            if "=" in line and not line.startswith("frame:"):
                try:
                    vals.append(float(line.strip().split("=", 1)[1]))
                except ValueError:
                    vals.append(-80.0)
    except FileNotFoundError:
        pass
    return vals


def _excess(rms, L):
    """Cuanto sube el volumen sobre lo normal de su alrededor (dB), suavizado."""
    r = [max(v, -80.0) for v in (rms + [-80.0] * L)[:L]]
    sm = []
    for i in range(L):
        w = r[max(0, i - 1):i + 2]
        sm.append(sum(w) / len(w))
    W = int(60 / STEP)
    base = [0.0] * L
    for i0 in range(0, L, 10):
        seg = sorted(sm[max(0, i0 - W):min(L, i0 + W)])
        med = seg[len(seg) // 2]
        for j in range(i0, min(L, i0 + 10)):
            base[j] = med
    score = [s_ - b for s_, b in zip(sm, base)]
    k = int(3 / STEP)
    val = []
    for i in range(L):
        w = score[max(0, i - k):i + k + 1]
        val.append(score[i] + 0.5 * (sum(w) / len(w)))
    return sm, score, val


def detect_moments(rms, a0, n, clip_len, total_dur, vrms=None):
    """rms: nivel (dB) cada STEP s desde a0. vrms: lo mismo pero solo en la banda de la voz (300-3400 Hz).
    Devuelve hasta n candidatos. Con voz, un momento solo vale si alguien habla/grita (no musica ni explosiones del juego)."""
    L = len(rms)
    if L < 20:
        return []
    sm, score, val = _excess(rms, L)
    vsm = vval = None
    if vrms and len(vrms) >= L * 0.9:
        vsm, _vs, vval = _excess(vrms, L)
        val = [0.45 * a + 0.75 * b for a, b in zip(val, vval)]
    order = sorted(range(L), key=lambda i: -val[i])
    picked, min_sep = [], max(clip_len * 1.2, 20) / STEP
    for i in order:
        if len(picked) >= n or val[i] < 2.0:
            break
        if vsm is not None and vsm[i] < -46:   # casi nadie hablando: ruido del juego
            continue
        if all(abs(i - j) >= min_sep for j in picked):
            picked.append(i)

    out = []
    for i in picked:
        t_peak = a0 + i * STEP
        before = sm[max(0, i - 16):max(1, i - 2)]
        spike = sm[i] - (statistics.median(before) if before else sm[i])
        around = score[max(0, i - 10):i + 11]
        sustain = sum(1 for x in around if x > 4) / max(1, len(around))
        if spike >= 15 and sustain < 0.5:
            cat = "susto"
        elif sustain >= 0.5:
            cat = "hype"
        else:
            cat = "fuerte"
        pre = clip_len * 0.6
        start = max(0.0, t_peak - pre)
        end = min(total_dur, start + clip_len)
        if end - start < clip_len * 0.8:
            start = max(0.0, end - clip_len)
        out.append({"t_peak": round(t_peak, 1), "start": round(start, 1), "end": round(end, 1),
                    "audio": round(min(10.0, val[i] / 2.0), 1), "intensity": round(min(10.0, val[i] / 2.0), 1),
                    "voice": round(min(10.0, (vval[i] if vval else val[i]) / 2.0), 1), "voice_db": round(vsm[i], 1) if vsm else None,
                    "visual": 0.0, "kw": 0.0, "cat": cat, "title": "", "reason": "", "transcript": ""})
    out.sort(key=lambda c: c["start"])
    return out


def visual_activity(job, low, start, dur):
    """Cuanta accion visual hay (cambios de escena / movimiento brusco) en una ventana. 0..10."""
    jd = job["dir"]
    (jd / "va.txt").unlink(missing_ok=True)
    subprocess.run(["ffmpeg", "-y", "-v", "error", "-nostdin", "-ss", f"{start:.2f}", "-t", f"{dur:.2f}", "-i", str(jd / low),
                    "-an", "-vf", "fps=4,scale=160:-2,select='gte(scene,0)',metadata=print:file=va.txt", "-f", "null", "-"],
                   cwd=jd, capture_output=True)
    vals = []
    try:
        for line in open(jd / "va.txt", errors="ignore"):
            if "lavfi.scene_score" in line:
                try:
                    vals.append(float(line.strip().split("=")[1]))
                except ValueError:
                    pass
    except FileNotFoundError:
        pass
    if not vals:
        return 0.0
    mean = sum(vals) / len(vals)
    top = sorted(vals)[-3:]
    return round(min(10.0, mean * 60 + (sum(top) / len(top)) * 8), 1)


def combined_score(c):
    ai = c.get("ai_score")
    base, vis, kw = c["audio"], c["visual"], min(c["kw"], 1.0)
    voice = c.get("voice", base)
    if ai is not None:
        sc = 0.3 * base + 0.2 * voice + 0.1 * vis + 0.5 * kw + 0.5 * ai
    else:
        sc = 0.35 * base + 0.4 * voice + 0.2 * vis + 1.0 * kw
    w = c.get("words")
    if w is not None:          # hay transcripcion: el silencio o 2 palabras sueltas no es un clip
        if w < 5:
            sc -= 2.5
        elif w >= 15:
            sc += 0.5
    return round(max(0.0, min(10.0, sc)), 1)


def why_text(c):
    """Explicacion corta de por que se eligio el momento (puntuacion de viralidad)."""
    r = []
    if c.get("reason"):
        r.append(c["reason"].rstrip("."))
    if c.get("voice", 0) >= 6:
        r.append("subes la voz de golpe (gritos o reacción fuerte)")
    elif c.get("audio", 0) >= 6:
        r.append("pico de volumen muy por encima de lo normal")
    if c.get("kw", 0) >= 0.5:
        r.append("lo que dices indica " + CAT_LABEL.get(c.get("cat"), "un momento fuerte").lower())
    if c.get("visual", 0) >= 5:
        r.append("mucha acción en pantalla")
    if c.get("words") is not None and c["words"] < 5:
        r.append("casi no se habla (puede ser flojo)")
    return ". ".join(x[0].upper() + x[1:] for x in r if x)[:220] or "Momento con más energía que el resto del directo"


def snap_bounds(c, total, clip_len):
    """Alinea el inicio/final del clip con frases completas (si hay transcripcion), para no cortar a media frase."""
    segs = c.get("segs") or []
    if not segs:
        return
    t0 = c["start"]
    ab = [(t0 + a, t0 + b) for a, b in segs]
    pk = c["t_peak"]
    cur = next((x for x in ab if x[0] <= pk <= x[1] + 0.6), None) or min(ab, key=lambda x: abs((x[0] + x[1]) / 2 - pk))
    prev = [x for x in ab if x[1] <= cur[0] and cur[0] - x[0] <= 7]
    st = (prev[0][0] if prev else cur[0]) - 1.0
    en = max(cur[1], pk) + 3.0
    lo, hi = clip_len * 0.6, clip_len * 1.35
    if en - st < lo:
        en = st + lo
    if en - st > hi:
        st = max(st, en - hi)
    st = max(0.0, st)
    en = min(total, en)
    if en - st >= 8:
        c["start"], c["end"] = round(st, 1), round(en, 1)


def extract_frames(path, stamps, prefix, cwd, width=384):
    out = []
    for k, t in enumerate(stamps):
        name = f"{prefix}{k}.jpg"
        r = subprocess.run(["ffmpeg", "-y", "-v", "error", "-nostdin", "-ss", f"{t:.2f}", "-i", str(path), "-frames:v", "1",
                            "-vf", f"scale='min({width},iw)':-2", "-q:v", "5", name], cwd=cwd, capture_output=True)
        if r.returncode == 0 and (cwd / name).exists():
            out.append((t, name))
    return out


def classify_with_ai(job, clips):
    low = job["dir"] / job["low"]
    dur = job["meta"]["duration"]
    content = []
    for c in clips:
        d = c["end"] - c["start"]
        stats = {"i": c["i"], "time_in_vod": hms(job["base_offset"] + c["t_peak"]), "audio_pattern": c["cat"],
                 "audio_intensity": c["audio"], "visual_activity": c["visual"]}
        if c["transcript"]:
            stats["transcript"] = c["transcript"][:600]
        content.append({"type": "text", "text": "Candidate: " + json.dumps(stats, ensure_ascii=False)})
        for k, frac in enumerate((0.25, 0.55, 0.85)):
            name = f"cf_{c['i']}_{k}.jpg"
            t = min(dur - 0.2, c["start"] + d * frac)
            r = subprocess.run(["ffmpeg", "-y", "-v", "error", "-nostdin", "-ss", f"{t:.2f}", "-i", str(low), "-frames:v", "1",
                                "-vf", "scale='min(384,iw)':-2", "-q:v", "6", name], cwd=job["dir"], capture_output=True)
            if r.returncode == 0 and (job["dir"] / name).exists():
                content.append(img_block(job["dir"] / name))
    content.append({"type": "text", "text": "Return the JSON array now."})
    arr = extract_json(call_claude(CLASSIFY_PROMPT, content, max_tokens=4000), "[")
    by_i = {c["i"]: c for c in clips}
    for o in arr:
        c = by_i.get(o.get("i"))
        if not c:
            continue
        if o.get("category") in ("risas", "terror", "polemica", "epico", "fail", "otro"):
            c["cat"] = o["category"]
        c["title"] = str(o.get("title", ""))[:70]
        c["reason"] = str(o.get("reason", ""))[:160]
        sc = clamp(o.get("score"), 1, 10, None)
        if sc is not None:
            c["ai_score"] = sc


# ---------------------------------------------------------------- camara
def detect_facecam_ai(job):
    frame = job["dir"] / "facecam_frame.jpg"
    text = call_claude(FACECAM_PROMPT, [img_block(frame), {"type": "text", "text": "Return the JSON now."}], max_tokens=300)
    o = extract_json(text, "{")
    if not o.get("found"):
        return None
    x, y, w, h = (clamp(o.get(k), 0, 1, None) for k in ("x", "y", "w", "h"))
    if None in (x, y, w, h) or w < 0.05 or h < 0.05 or w > 0.7 or h > 0.7:
        return None
    x, y = min(x, 1 - w), min(y, 1 - h)
    return {"x": round(x, 4), "y": round(y, 4), "w": round(w, 4), "h": round(h, 4)}


def _is_skin(r, g, b):
    if r < 60:
        return False
    cb = 128 - 0.168736 * r - 0.331264 * g + 0.5 * b
    cr = 128 + 0.5 * r - 0.418688 * g - 0.081312 * b
    return 77 <= cb <= 127 and 133 <= cr <= 173


def detect_facecam_basic(job, times):
    """Busca la camara sin IA: una esquina con mucho color de piel que se repite en varios fotogramas."""
    FW, FH = 192, 108
    low = job["dir"] / job["low"]
    frames = []
    for t in times:
        r = subprocess.run(["ffmpeg", "-v", "error", "-nostdin", "-ss", f"{t:.2f}", "-i", str(low), "-frames:v", "1",
                            "-vf", f"scale={FW}:{FH}", "-f", "rawvideo", "-pix_fmt", "rgb24", "-"], capture_output=True)
        if len(r.stdout) == FW * FH * 3:
            frames.append(r.stdout)
    if len(frames) < 2:
        return None
    rw, rh = int(FW * 0.36), int(FH * 0.44)
    regions = {"tl": (0, 0), "tr": (FW - rw, 0), "bl": (0, FH - rh), "br": (FW - rw, FH - rh)}
    cx0, cy0 = (FW - rw) // 2, (FH - rh) // 2
    counts = {}
    for name, (x0, y0) in list(regions.items()) + [("c", (cx0, cy0))]:
        grid = [[0] * rw for _ in range(rh)]
        for raw in frames:
            for yy in range(rh):
                base = ((y0 + yy) * FW + x0) * 3
                row = grid[yy]
                for xx in range(rw):
                    i = base + xx * 3
                    if _is_skin(raw[i], raw[i + 1], raw[i + 2]):
                        row[xx] += 1
        counts[name] = grid
    nf = len(frames)
    ratio = {k: sum(sum(1 for v in row if v) for row in g) / float(rw * rh * nf) for k, g in counts.items()}
    corner = max(regions, key=lambda k: ratio[k])
    if ratio[corner] < 0.04 or ratio[corner] < 1.6 * ratio["c"]:
        return None
    grid, (x0, y0) = counts[corner], regions[corner]
    need = max(1, math.ceil(0.5 * nf))
    pts = [(xx, yy) for yy in range(rh) for xx in range(rw) if grid[yy][xx] >= need] or \
          [(xx, yy) for yy in range(rh) for xx in range(rw) if grid[yy][xx] >= 1]
    if not pts:
        return None
    bx0, bx1 = min(p[0] for p in pts) + x0, max(p[0] for p in pts) + x0
    by0, by1 = min(p[1] for p in pts) + y0, max(p[1] for p in pts) + y0
    bw, bh = max(1, bx1 - bx0), max(1, by1 - by0)
    padx, pady = 0.7 * bw, 0.8 * bh
    if corner[1] == "r":
        left, right = bx0 - padx, FW
    else:
        left, right = 0, bx1 + padx
    if corner[0] == "b":
        top, bottom = by0 - pady, FH
    else:
        top, bottom = 0, by1 + pady
    left, right = max(0, left), min(FW, right)
    top, bottom = max(0, top), min(FH, bottom)
    w, h = (right - left) / FW, (bottom - top) / FH
    w, h = min(max(w, 0.16), 0.5), min(max(h, 0.2), 0.55)
    x = (1 - w) if corner[1] == "r" else 0.0
    y = (1 - h) if corner[0] == "b" else 0.0
    return {"x": round(x, 4), "y": round(y, 4), "w": round(w, 4), "h": round(h, 4)}


# ---------------------------------------------------------------- analisis completo
def analyze_job(job):
    p = job["params"]
    jd = job["dir"]
    try:
        job["status"] = "running"
        if p["url"]:
            setp(job, 2, "Descargando el VOD en baja calidad (para analizarlo rápido)…")
            low = download_low(job)
        else:
            low = p["file_name"]
            job["base_offset"] = 0
        low, meta = make_playable(job, low)
        job["low"], job["meta"] = low, meta
        job["has_audio"] = meta["has_audio"]
        if not meta["has_audio"]:
            raise RuntimeError("El video no tiene audio, y busco los momentos por el audio.")
        setp(job, 38, f"VOD listo: {hms(meta['duration'])} de duración")

        a0, adur = 0.0, meta["duration"]
        if not p["url"]:
            if p["t_from"]:
                a0 = min(p["t_from"], max(0, meta["duration"] - 10))
            adur = (max(10.0, min(p["t_to"], meta["duration"]) - a0) if p["t_to"] else meta["duration"] - a0)
        setp(job, 40, "Analizando el audio (gritos, risas, picos de volumen)…")
        n_samp = int(16000 * STEP)
        fg = (f"[0:a]aformat=channel_layouts=mono,aresample=16000,asplit=2[x][y];"
              f"[x]asetnsamples=n={n_samp}:p=0,astats=metadata=1:reset=1,"
              f"ametadata=mode=print:key=lavfi.astats.Overall.RMS_level:file=rms.txt[o1];"
              f"[y]highpass=f=250,lowpass=f=3400,asetnsamples=n={n_samp}:p=0,astats=metadata=1:reset=1,"
              f"ametadata=mode=print:key=lavfi.astats.Overall.RMS_level:file=voice.txt[o2]")
        (jd / "rms.txt").unlink(missing_ok=True)
        (jd / "voice.txt").unlink(missing_ok=True)
        try:
            run_ffmpeg(job, ["-ss", f"{a0:.2f}", "-t", f"{adur:.2f}", "-i", low, "-vn", "-filter_complex", fg,
                             "-map", "[o1]", "-f", "null", "-", "-map", "[o2]", "-f", "null", "-"],
                       "audio", total=adur, p0=40, p1=70)
        except RuntimeError:
            (jd / "voice.txt").unlink(missing_ok=True)
            af = (f"aresample=16000,asetnsamples=n={n_samp}:p=0,astats=metadata=1:reset=1,"
                  f"ametadata=mode=print:key=lavfi.astats.Overall.RMS_level:file=rms.txt")
            run_ffmpeg(job, ["-ss", f"{a0:.2f}", "-t", f"{adur:.2f}", "-i", low, "-vn", "-ac", "1", "-af", af, "-f", "null", "-"],
                       "audio", total=adur, p0=40, p1=70)
        rms = read_series(jd / "rms.txt")
        vrms = read_series(jd / "voice.txt")
        # saco muchos candidatos y me quedo con los mejores (asi de 15 clips salen casi todos buenos)
        pool_n = min(60, max(p["n_clips"] + 4, p["n_clips"] * 3))
        clips = detect_moments(rms, a0, pool_n, p["clip_len"], meta["duration"], vrms=vrms)
        if not clips:
            raise RuntimeError("No encontré picos de audio claros. Prueba con otro rango o un directo con más reacciones.")
        for k, c in enumerate(clips):
            c["i"] = k
        job["log"].append(f"Encontré {len(clips)} momentos candidatos")

        setp(job, 72, "Sacando miniaturas y midiendo la acción…")
        for k, c in enumerate(clips):
            if job["cancel"]:
                raise Cancelled()
            name = f"thumb_{c['i']}.jpg"
            subprocess.run(["ffmpeg", "-y", "-v", "error", "-nostdin", "-ss", f"{c['t_peak']:.2f}", "-i", str(jd / low),
                            "-frames:v", "1", "-vf", "scale='min(480,iw)':-2", "-q:v", "5", name], cwd=jd, capture_output=True)
            c["thumb"] = name if (jd / name).exists() else ""
            c["visual"] = visual_activity(job, low, c["start"], min(c["end"] - c["start"], 40))
            setp(job, 72 + 8 * (k + 1) / len(clips))

        # camara
        setp(job, 80, "Buscando tu cámara…")
        order = sorted(clips, key=lambda c: -c["audio"])
        best = order[0]
        subprocess.run(["ffmpeg", "-y", "-v", "error", "-nostdin", "-ss", f"{best['t_peak']:.2f}", "-i", str(jd / low),
                        "-frames:v", "1", "-vf", "scale='min(960,iw)':-2", "-q:v", "3", "facecam_frame.jpg"],
                       cwd=jd, capture_output=True)
        job["facecam"], job["facecam_src"] = None, ""
        if get_key("anthropic_key"):
            try:
                fc = detect_facecam_ai(job)
                if fc:
                    job["facecam"], job["facecam_src"] = fc, "ia"
            except Cancelled:
                raise
            except Exception as e:
                job["log"].append(f"La IA no pudo ubicar la cámara ({str(e)[:100]}).")
        if not job["facecam"]:
            try:
                times = [c["t_peak"] for c in order[:6]]
                fc = detect_facecam_basic(job, times)
                if fc:
                    job["facecam"], job["facecam_src"] = fc, "auto"
            except Exception as e:
                job["log"].append(f"No pude buscar la cámara automáticamente: {str(e)[:100]}")
        if not job["facecam"]:
            job["facecam"] = {"x": 0.74, "y": 0.60, "w": 0.25, "h": 0.37}
            job["facecam_src"] = "guess"
        setp(job, 84, {"ia": "Cámara encontrada con IA", "auto": "Cámara encontrada (revísala)",
                       "guess": "No encontré la cámara: márcala tú"}[job["facecam_src"]])

        # transcripcion + clasificacion
        if get_key("openai_key"):
            setp(job, 85, "Transcribiendo los momentos…")
            for k, c in enumerate(clips[:45]):
                if job["cancel"]:
                    raise Cancelled()
                try:
                    cut_audio(job, low, c["start"], c["end"] - c["start"], "cand.mp3")
                    wd = whisper(jd / "cand.mp3", verbose=True)
                    c["transcript"] = (wd.get("text") or "").strip()
                    c["words"] = len(re.findall(r"\w+", c["transcript"]))
                    c["segs"] = [(round(x["start"], 2), round(x["end"], 2)) for x in (wd.get("segments") or [])][:40]
                    cat, bonus = keyword_scan(c["transcript"])
                    c["kw"] = bonus
                    if cat:
                        c["cat"] = cat
                except Cancelled:
                    raise
                except Exception as e:
                    job["log"].append(f"No pude transcribir: {str(e)[:100]}")
                    break
                setp(job, 85 + 5 * (k + 1) / len(clips))
        job["ai_used"] = False
        if get_key("anthropic_key"):
            setp(job, 91, "La IA está revisando cada momento…")
            try:
                classify_with_ai(job, clips)
                job["ai_used"] = True
            except Cancelled:
                raise
            except Exception as e:
                job["log"].append(f"La IA no pudo clasificar ({str(e)[:120]}); uso solo el audio.")

        # ranking final: me quedo con los mejores
        for c in clips:
            c["intensity"] = combined_score(c)
        ranked = sorted(clips, key=lambda c: -c["intensity"])
        good = [c for c in ranked if c["intensity"] >= 4.0]
        keep = max(3, int(p["n_clips"] * 0.6))
        top = (good if len(good) >= keep else ranked)[:p["n_clips"]]
        job["log"].append(f"De {len(clips)} momentos candidatos elegí los {len(top)} mejores ({len(good)} con nota alta).")
        for c in top:
            snap_bounds(c, meta["duration"], p["clip_len"])
            c["why"] = why_text(c)
            c.pop("segs", None)
        top.sort(key=lambda c: c["start"])
        for k, c in enumerate(top):
            c["i"] = k
            if not c["title"]:
                c["title"] = f"{CAT_LABEL.get(c['cat'], 'Momento')} · {hms(job['base_offset'] + c['t_peak'])}"
        job["clips"] = top
        job["status"] = "ready"
        setp(job, 100, "¡Listo! Elige tus clips")
        save_job(job)
        if job["auto"]:
            if job["facecam_src"] == "guess":
                job["log"].append("No encontré tu cámara: usé una posición por defecto. Ajústala y pulsa 'Guardar cámara' para rehacer.")
            start_export(job, [{"i": c["i"], "start": c["start"], "end": c["end"], "title": c["title"],
                                "layout": ""} for c in top], job["settings"])
        save_job(job)
    except Cancelled:
        job["status"] = "cancelled"
        job["stage"] = "Cancelado"
        save_job(job)
    except Exception as e:
        job["status"] = "error"
        job["error"] = str(e)
        job["log"].append("Error: " + str(e))
        save_job(job)


# ---------------------------------------------------------------- ajustes de los clips
LAYOUTS = ("auto", "split", "circle", "cam", "game", "horizontal", "fill", "dual")
ASSET_RE = re.compile(r"^[A-Za-z0-9_.-]{1,90}$")
DEFAULT_SETTINGS = {
    "layout": "auto", "cam_order": "top", "split_pct": 38, "resolution": "1080", "fps": "30", "quality": "alta",
    "normalize": True, "titles": True, "captions": True, "caption_style": "karaoke", "zoom_peak": True,
    "sfx": "none", "follow_action": False, "music": "", "music_volume": 0.18, "music_duck": True,
    "logo": "", "logo_pos": "tr", "intro_text": "", "outro_text": "", "game_fit": "blur", "game_x": 50,
    "circle_pos": "br", "auto_create": True,
    "mute_profanity": False, "profanity_sound": "mute", "overlays": [],
}


def asset_path(name):
    if name and ASSET_RE.match(name):
        p = ASSETS_DIR / name
        if p.is_file():
            return p
    return None


def sanitize_bg(b):
    b = b if isinstance(b, dict) else {}
    hx = lambda v, d: (str(v or "").lstrip("#").lower() if re.fullmatch(r"#?[0-9a-fA-F]{6}", str(v or "")) else d)
    return {"mode": "chroma" if b.get("mode") == "chroma" else "none", "color": hx(b.get("color"), "00ff00"),
            "sim": round(clamp(b.get("sim"), 0.02, 0.6, 0.25), 2), "back": "image" if b.get("back") == "image" else "color",
            "bgcolor": hx(b.get("bgcolor"), "000000"), "bgimg": str(b.get("bgimg") or "") if asset_path(str(b.get("bgimg") or "")) else ""}


def sanitize_overlays(lst):
    """Textos e imagenes puestos encima del clip (como en CapCut). x,y = centro (0-1); size = fraccion del ancho."""
    out = []
    for o in (lst or [])[:12]:
        if not isinstance(o, dict):
            continue
        typ = o.get("type")
        if typ == "text":
            txt = str(o.get("text", "")).strip()[:100]
            if not txt:
                continue
            col = str(o.get("color", "ffffff")).lstrip("#")
            col = col if re.fullmatch(r"[0-9a-fA-F]{6}", col) else "ffffff"
            bg = o.get("bg") if o.get("bg") in ("none", "outline", "card", "box") else "outline"
            d = {"type": "text", "text": txt, "color": col.lower(), "bg": bg,
                 "size": round(clamp(o.get("size"), 0.025, 0.2, 0.06), 3)}
        elif typ == "image":
            nm = str(o.get("asset", ""))
            if not asset_path(nm):
                continue
            d = {"type": "image", "asset": nm, "size": round(clamp(o.get("size"), 0.04, 1.0, 0.2), 3)}
        else:
            continue
        d["x"] = round(clamp(o.get("x"), 0, 1, 0.5), 3)
        d["y"] = round(clamp(o.get("y"), 0, 1, 0.1), 3)
        d["t0"] = round(clamp(o.get("t0"), 0, 600, 0), 2)
        t1 = o.get("t1")
        d["t1"] = -1 if t1 in (None, "", -1) else round(clamp(t1, 0, 600, -1), 2)
        out.append(d)
    return out


def sanitize_settings(s0, base=None):
    s = dict(DEFAULT_SETTINGS)
    s.update({k: v for k, v in (base or {}).items() if k in DEFAULT_SETTINGS})
    s0 = s0 or {}

    def pick(k, allowed):
        v = s0.get(k, s[k])
        if isinstance(v, (int, float)) and not isinstance(v, bool):
            v = str(int(v)) if k in ("resolution", "fps") else v
        return v if v in allowed else s[k]

    def flag(k):
        return bool(s0[k]) if k in s0 else bool(s[k])

    s["layout"] = pick("layout", LAYOUTS)
    s["cam_order"] = pick("cam_order", ("top", "bottom"))
    s["split_pct"] = int(clamp(s0.get("split_pct", s["split_pct"]), 20, 60, 38))
    s["resolution"] = pick("resolution", ("480", "720", "1080"))
    s["fps"] = pick("fps", ("original", "24", "30", "60"))
    s["quality"] = pick("quality", ("alta", "media", "baja"))
    for k in ("normalize", "titles", "captions", "zoom_peak", "follow_action", "music_duck", "auto_create", "mute_profanity"):
        s[k] = flag(k)
    s["overlays"] = sanitize_overlays(s0["overlays"]) if "overlays" in s0 else sanitize_overlays(s.get("overlays"))
    s["profanity_sound"] = pick("profanity_sound", ("mute", "beep", "low"))
    s["caption_style"] = pick("caption_style", ("karaoke", "simple"))
    s["sfx"] = pick("sfx", ("none", "boom", "whoosh", "ding"))
    s["music_volume"] = round(clamp(s0.get("music_volume", s["music_volume"]), 0.03, 0.6, 0.18), 3)
    for k in ("music", "logo"):
        v = str(s0.get(k, s[k]) or "")
        s[k] = v if asset_path(v) else ""
    s["logo_pos"] = pick("logo_pos", ("tl", "tr", "bl", "br"))
    for k in ("intro_text", "outro_text"):
        s[k] = str(s0.get(k, s[k]) or "").strip()[:80]
    s["game_fit"] = pick("game_fit", ("blur", "crop"))
    s["game_x"] = int(clamp(s0.get("game_x", s["game_x"]), 0, 100, 50))
    s["circle_pos"] = pick("circle_pos", ("br", "bl", "tr", "tl", "bc"))
    return s


# ---------------------------------------------------------------- geometria
def out_dims(layout, resolution):
    res = int(resolution)
    if layout == "horizontal":
        return even(res * 16 / 9), even(res)
    return even(res), even(res * 16 / 9)


def game_region(inl, outl, W, H, fit, gx):
    """El gameplay llenando un rectangulo WxH. gx: numero 0..1 o expresion de ffmpeg (en t)."""
    if fit == "crop":
        return (f"[{inl}]scale={W}:{H}:force_original_aspect_ratio=increase,"
                f"crop={W}:{H}:x='(iw-ow)*({gx})':y='(ih-oh)/2'[{outl}]")
    return (f"[{inl}]split=2[{outl}a][{outl}b];"
            f"[{outl}a]scale={W}:{H}:force_original_aspect_ratio=increase,crop={W}:{H},boxblur=20:2[{outl}bg];"
            f"[{outl}b]scale={W}:{H}:force_original_aspect_ratio=decrease[{outl}fg];"
            f"[{outl}bg][{outl}fg]overlay=(W-w)/2:(H-h)/2[{outl}]")


def cam_rect_px(fc, sw, sh):
    cw = min(even(fc["w"] * sw), even(sw))
    ch = min(even(fc["h"] * sh), even(sh))
    cx = max(0, min(even(fc["x"] * sw), sw - cw))
    cy = max(0, min(even(fc["y"] * sh), sh - ch))
    return cx, cy, cw, ch


def make_circle_assets(job, D):
    jd = job["dir"]
    if (jd / f"mask_{D}.png").exists() and (jd / f"ring_{D}.png").exists():
        return f"mask_{D}.png", f"ring_{D}.png"
    R = D / 2.0
    mask = f"clip(({R}-hypot(X-{R}+0.5,Y-{R}+0.5))*2,0,1)*255"
    band = max(4, D // 40)
    ring = f"clip(({R}-hypot(X-{R}+0.5,Y-{R}+0.5))*2,0,1)*clip((hypot(X-{R}+0.5,Y-{R}+0.5)-({R}-{band}))*2,0,1)*255"
    run_ffmpeg(job, ["-f", "lavfi", "-i", f"nullsrc=s={D}x{D}:d=1,format=gray,geq=lum='{mask}'", "-frames:v", "1",
                     f"mask_{D}.png"], "mask")
    run_ffmpeg(job, ["-f", "lavfi", "-i", f"nullsrc=s={D}x{D}:d=1,format=rgba,geq=r=255:g=255:b=255:a='{ring}'",
                     "-frames:v", "1", "-pix_fmt", "rgba", f"ring_{D}.png"], "ring")
    return f"mask_{D}.png", f"ring_{D}.png"


def pl_expr(pts):
    """Interpolacion lineal por tramos en t: pts = [(t, valor), ...]."""
    if len(pts) == 1:
        return f"{pts[0][1]:.4f}"
    e = f"{pts[-1][1]:.4f}"
    for (t0, v0), (t1, v1) in reversed(list(zip(pts, pts[1:]))):
        e = f"if(lt(t,{t1:.2f}),{v0:.4f}+({v1 - v0:.4f})*(t-{t0:.2f})/{max(0.01, t1 - t0):.2f},{e})"
    return e


def motion_track(src, ss, dur, region_w, region_h, sw, sh, fc):
    """Sigue la accion: donde hay mas movimiento (horizontal). Devuelve [(t, gx 0..1)] o None."""
    w, h = 64, 36
    r = subprocess.run(["ffmpeg", "-v", "error", "-nostdin", "-ss", f"{ss:.2f}", "-t", f"{dur:.2f}", "-i", str(src), "-an",
                        "-vf", f"fps=5,scale={w}:{h},format=gray", "-f", "rawvideo", "-"], capture_output=True)
    raw = r.stdout
    nfr = len(raw) // (w * h)
    if nfr < 6:
        return None
    scale = max(region_w / float(sw), region_h / float(sh))
    iw, ow = sw * scale, float(region_w)
    if iw <= ow + 2:
        return None
    mx0 = mx1 = my0 = my1 = -1
    if fc:
        mx0, mx1 = int(fc["x"] * w) - 1, int((fc["x"] + fc["w"]) * w) + 1
        my0, my1 = int(fc["y"] * h) - 1, int((fc["y"] + fc["h"]) * h) + 1
    cents = []
    prev = raw[:w * h]
    for f in range(1, nfr):
        cur = raw[f * w * h:(f + 1) * w * h]
        e_tot, e_x = 0.0, 0.0
        for y in range(h):
            row = y * w
            for x in range(w):
                if mx0 <= x <= mx1 and my0 <= y <= my1:
                    continue
                d = abs(cur[row + x] - prev[row + x])
                if d > 12:
                    e_tot += d
                    e_x += d * x
        cents.append((f / 5.0, (e_x / e_tot) / (w - 1) if e_tot > 60 else None))
        prev = cur
    pts, last, gx_prev = [], 0.5, 0.5
    for sec in range(0, int(dur) + 1):
        vals = [c for (t, c) in cents if sec - 0.5 <= t < sec + 0.5 and c is not None]
        c = sum(vals) / len(vals) if vals else last
        last = c
        c = 0.35 * 0.5 + 0.65 * c
        gx = (c * iw - ow / 2.0) / (iw - ow)
        gx = min(1.0, max(0.0, gx))
        gx = gx_prev + max(-0.25, min(0.25, 0.6 * (gx - gx_prev)))
        gx_prev = gx
        pts.append((float(sec), gx))
    return pts[:60] if len(pts) > 1 else None


# ---------------------------------------------------------------- sonidos y textos
def sfx_asset(kind):
    p = ASSETS_DIR / f"sfx_{kind}.wav"
    if p.exists():
        return p
    fmt = "aformat=sample_rates=44100:channel_layouts=stereo"
    if kind == "boom":
        args = ["-f", "lavfi", "-i", "sine=f=50:d=1.0", "-f", "lavfi", "-i", "anoisesrc=d=0.4:c=brown:a=0.8",
                "-filter_complex", f"[0]afade=t=out:st=0.05:d=0.95,volume=2.2[a];[1]afade=t=out:st=0:d=0.4[b];"
                                   f"[a][b]amix=inputs=2:normalize=0,{fmt},alimiter=limit=0.9"]
    elif kind == "whoosh":
        args = ["-f", "lavfi", "-i", "anoisesrc=d=0.8:c=pink:a=0.7", "-af",
                f"highpass=f=300,lowpass=f=5000,afade=t=in:st=0:d=0.4,afade=t=out:st=0.4:d=0.4,{fmt}"]
    else:
        args = ["-f", "lavfi", "-i", "sine=f=1480:d=0.9", "-af", f"afade=t=out:st=0.02:d=0.88,volume=0.7,{fmt}"]
    subprocess.run(["ffmpeg", "-y", "-v", "error", "-nostdin"] + args + [str(p)], check=True, capture_output=True)
    return p


def wrap_lines(text, width):
    words, lines, cur = text.split(), [], ""
    for w in words:
        if len(cur) + len(w) + 1 > width and cur:
            lines.append(cur)
            cur = w
        else:
            cur = (cur + " " + w).strip()
    if cur:
        lines.append(cur)
    return "\n".join(lines[:3]) or text


_PROF = re.compile(
    r"^(hij[oa]?p[uo]?t[ao]s?|hueput[ao]s?|hijueput[ao]s?|hpt[ao]?|hp|gonorre[ao]s?|malparid[oa]s?|maric[ao]s?|maricon(es)?|"
    r"put[ao]s?|mierd[ao]s?|carajo|co[ñn]o|jod(er|ido|ida|idos|e)|verg[ao]s?|pendej[oa]s?|cabron(es|a|as)?|chingad[oa]s?|"
    r"chinga(r|n|s)?|culer[oa]s?|pinche|mamaguev[oa]s?|guevon(es|a)?|huevon(es|a)?|cojud[oa]s?|cag(ar|ada|ado|ue|o|on|ones)|"
    r"culo|culos|fuck\w*|shit\w*|bitch\w*|asshole|cunt|dick|motherfucker\w*|nigg\w+|puñeta|puneta|gilipollas|zorra|perra)$")


def _norm_word(w):
    w = unicodedata.normalize("NFKD", str(w).lower())
    w = "".join(ch for ch in w if not unicodedata.combining(ch))
    return re.sub(r"[^a-zñ0-9]", "", w)


def is_profane(w):
    n = _norm_word(w)
    return bool(n) and bool(_PROF.match(n))


def profane_ranges(words, dur):
    """Rangos (inicio, fin) en segundos de cada palabra grosera. 'hijo de puta' tapa las 3 palabras."""
    out = []
    ws = [(w, _norm_word(w.get("word", ""))) for w in words]
    k = 0
    while k < len(ws):
        w, n = ws[k]
        hit = 1 if is_profane(w.get("word", "")) else 0
        if not hit and n in ("hijo", "hija") and k + 2 < len(ws) + 0 and ws[k + 1][1] == "de" and ws[k + 2][1].startswith("put"):
            hit = 3
        if hit:
            a = max(0.0, float(w["start"]) - 0.06)
            b = min(dur, float(ws[k + hit - 1][0]["end"]) + 0.14)
            if b > a:
                out.append((a, b))
            k += hit
        else:
            k += 1
    return out[:80]


def censor_text(t):
    return " ".join((x[0] + "*" * max(2, len(x) - 1)) if is_profane(x) else x for x in str(t).split())


def drawtext(jd, name, text, fs, color, y_expr, t0, t1, W, font, box=False, upper=False, fade=True, card=False, x_expr="(w-text_w)/2"):
    if upper:
        text = text.upper()
    (jd / f"{name}.txt").write_text(wrap_lines(text, max(8, int(W * 0.88 / (fs * 0.56)))), encoding="utf-8")
    alpha = (f"if(lt(t\\,{t0:.2f}+0.2)\\,(t-{t0:.2f})/0.2\\,if(gt(t\\,{t1:.2f}-0.2)\\,({t1:.2f}-t)/0.2\\,1))"
             if fade else "1")
    ff = f"fontfile='{font}':" if font else ""
    boxopt = f":box=1:boxcolor=black@0.55:boxborderw={fs // 3}" if box else ""
    if card:  # tarjeta blanca con texto negro (estilo StreamLadder)
        boxopt = f":box=1:boxcolor=white@0.96:boxborderw={fs // 2}"
        return (f"drawtext={ff}textfile={name}.txt:expansion=none:fontsize={fs}:fontcolor=0x111111:"
                f"line_spacing={fs // 5}:x={x_expr}:y={y_expr}:alpha='{alpha}':"
                f"enable='between(t\\,{t0:.2f}\\,{t1:.2f})'{boxopt}")
    return (f"drawtext={ff}textfile={name}.txt:expansion=none:fontsize={fs}:fontcolor=0x{color}:"
            f"borderw={max(2, fs // 14)}:bordercolor=black@0.9:shadowx=2:shadowy=2:line_spacing={fs // 6}:"
            f"x={x_expr}:y={y_expr}:alpha='{alpha}':enable='between(t\\,{t0:.2f}\\,{t1:.2f})'{boxopt}")


def caption_items(data, dur):
    """Frases cortas para los subtitulos simples: [(t0, t1, texto)]."""
    words = data.get("words") or []
    items = []
    if words:
        chunk = []
        for w in words:
            chunk.append(w)
            txt = " ".join(x["word"].strip() for x in chunk)
            if len(chunk) >= 4 or len(txt) >= 22 or re.search(r"[.!?,;]$", w["word"].strip()):
                items.append((chunk[0]["start"], chunk[-1]["end"], txt))
                chunk = []
        if chunk:
            items.append((chunk[0]["start"], chunk[-1]["end"], " ".join(x["word"].strip() for x in chunk)))
    else:
        for sgm in data.get("segments") or []:
            items.append((sgm["start"], sgm["end"], sgm["text"].strip()))
    out = []
    for k, (a, b, t) in enumerate(items):
        nxt = items[k + 1][0] if k + 1 < len(items) else dur
        b = min(max(b, a + 0.3), nxt if nxt > a + 0.3 else b)
        if t:
            out.append((a, min(b + 0.15, dur), t))
    return out[:90]


def ass_ts(t):
    t = max(0.0, t)
    return f"{int(t // 3600)}:{int(t % 3600 // 60):02d}:{t % 60:05.2f}"


def ass_clean(w):
    return re.sub(r"[{}\\\r\n]", "", str(w)).strip()


def make_ass(path, cap, W, H, fontname, dur):
    """Subtitulos estilo TikTok: grupos de 1-3 palabras y la que se dice resaltada en amarillo."""
    fs = int(min(W, H) * 0.085)
    outline = max(3, fs // 12)
    y = int(H * (0.70 if H >= W else 0.84))
    lines = ["[Script Info]", "ScriptType: v4.00+", f"PlayResX: {W}", f"PlayResY: {H}", "WrapStyle: 2",
             "ScaledBorderAndShadow: yes", "", "[V4+ Styles]",
             "Format: Name, Fontname, Fontsize, PrimaryColour, SecondaryColour, OutlineColour, BackColour, Bold, Italic, "
             "Underline, StrikeOut, ScaleX, ScaleY, Spacing, Angle, BorderStyle, Outline, Shadow, Alignment, MarginL, "
             "MarginR, MarginV, Encoding",
             f"Style: Cap,{fontname},{fs},&H00FFFFFF,&H00FFFFFF,&H00000000,&H64000000,-1,0,0,0,100,100,0,0,1,{outline},2,5,"
             f"40,40,0,1", "", "[Events]", "Format: Layer, Start, End, Style, Name, MarginL, MarginR, MarginV, Effect, Text"]
    n_ev = 0
    pos = "\\an5\\pos(%d,%d)" % (W // 2, y)
    words = [w for w in (cap.get("words") or []) if ass_clean(w.get("word", ""))]
    if words:
        groups, cur = [], []
        for w in words:
            cur.append({"w": ass_clean(w["word"]), "s": float(w["start"]), "e": float(w["end"])})
            total = sum(len(x["w"]) for x in cur) + len(cur) - 1
            if len(cur) >= 3 or total >= 16 or re.search(r"[.!?,;:]$", cur[-1]["w"]):
                groups.append(cur)
                cur = []
        if cur:
            groups.append(cur)
        for g in groups:
            for j, wd in enumerate(g):
                t0 = wd["s"]
                t1 = g[j + 1]["s"] if j + 1 < len(g) else wd["e"] + 0.12
                t1 = max(t1, t0 + 0.08)
                if t0 >= dur:
                    continue
                parts = [("{\\c&H00E6FF&}" if k == j else "{\\c&HFFFFFF&}") + x["w"].upper() for k, x in enumerate(g)]
                text = "{" + pos + "\\fscx88\\fscy88\\t(0,80,\\fscx100\\fscy100)}" + " ".join(parts)
                lines.append(f"Dialogue: 0,{ass_ts(t0)},{ass_ts(min(t1, dur))},Cap,,0,0,0,,{text}")
                n_ev += 1
    else:
        for sg in cap.get("segments") or []:
            t = ass_clean(sg.get("text", "")).upper()
            if t and float(sg["start"]) < dur:
                lines.append(f"Dialogue: 0,{ass_ts(float(sg['start']))},{ass_ts(min(float(sg['end']), dur))},Cap,,0,0,0,,"
                             "{" + pos + "}" + t)
                n_ev += 1
    Path(path).write_text("\n".join(lines) + "\n", encoding="utf-8")
    return n_ev


def render_card(job, name, text, W, H, fps, font):
    jd = job["dir"]
    dur = 2.0
    fs = int(H * 0.075)
    (jd / f"{name}_t.txt").write_text(wrap_lines(text, max(8, int(W * 0.86 / (fs * 0.56)))), encoding="utf-8")
    ff = f"fontfile='{font}':" if font else ""
    alpha = "if(lt(t\\,0.4)\\,t/0.4\\,if(gt(t\\,1.7)\\,(2.0-t)/0.3\\,1))"
    dt = (f"drawtext={ff}textfile={name}_t.txt:expansion=none:fontsize={fs}:fontcolor=white:borderw={max(2, fs // 14)}:"
          f"bordercolor=black@0.9:line_spacing={fs // 6}:x=(w-text_w)/2:y=(h-text_h)/2:alpha='{alpha}'")
    run_ffmpeg(job, ["-f", "lavfi", "-i", f"color=c=0x101018:s={W}x{H}:r={fps}:d={dur}",
                     "-f", "lavfi", "-i", "anullsrc=r=44100:cl=stereo", "-t", f"{dur}",
                     "-vf", f"vignette=PI/5,{dt},format=yuv420p", "-c:v", "libx264", "-preset", "ultrafast", "-crf", "20",
                     "-pix_fmt", "yuv420p", "-c:a", "aac", "-b:a", "128k", "-ar", "44100", "-ac", "2", f"{name}.mp4"], name)
    return f"{name}.mp4"


# ---------------------------------------------------------------- render de un clip
def download_clip_source(job, abs_start, abs_end, n, cap):
    cmd = ytdlp_cmd()
    if not cmd and not is_hls(job["params"]["url"]):
        return None
    for old in job["dir"].glob(f"clipsrc_{n}.*"):
        old.unlink()
    url = job["params"]["url"]
    if is_hls(url):
        out = f"clipsrc_{n}.mp4"
        r = subprocess.run(["ffmpeg", "-y", "-v", "error", "-nostdin"] + hls_headers(url) +
                           ["-ss", f"{abs_start:.2f}", "-t", f"{abs_end - abs_start:.2f}", "-i", url, "-vf",
                            f"scale=-2:'min({cap},ih)'", "-c:v", "libx264", "-preset", "veryfast", "-crf", "23",
                            "-c:a", "aac", "-b:a", "128k", out], cwd=job["dir"], capture_output=True, text=True)
        return out if r.returncode == 0 and (job["dir"] / out).exists() else None
    args = cmd + ["--no-playlist", "--newline", "--no-warnings", "--concurrent-fragments", "4",
                  "-f", f"b[height<={cap}]/b/w", "--merge-output-format", "mp4",
                  "--download-sections", f"*{abs_start:.1f}-{abs_end:.1f}", "-o", f"clipsrc_{n}.%(ext)s"] + dl_extra(url) + [url]
    r = subprocess.run(args, cwd=job["dir"], capture_output=True, text=True)
    files = [f for f in job["dir"].glob(f"clipsrc_{n}.*") if f.suffix not in (".part", ".ytdl")]
    return files[0].name if r.returncode == 0 and files else None


def default_cam():
    return {"x": 0.74, "y": 0.60, "w": 0.25, "h": 0.37}


def detect_dual_screen(path, ss, dur, sw, sh):
    """Detecta si el video ya trae DOS pantallas (lado a lado o arriba/abajo) separadas por una costura recta.
    Devuelve {"axis": "v"|"h", "pos": 0..1} o None."""
    FW, FH = 320, 180
    fr = []
    for f in (0.1, 0.3, 0.5, 0.7, 0.9):
        try:
            r = subprocess.run(["ffmpeg", "-v", "error", "-nostdin", "-ss", f"{max(0.0, ss + dur * f):.2f}", "-i", str(path),
                                "-frames:v", "1", "-vf", f"scale={FW}:{FH},format=gray", "-f", "rawvideo", "-"],
                               capture_output=True, timeout=60)
        except Exception:
            continue
        if len(r.stdout) == FW * FH:
            fr.append(r.stdout)
    if len(fr) < 3:
        return None
    TH = 18  # salto de brillo que cuenta como "borde"

    def seams(raw, axis):
        out = {}
        if axis == "v":
            lo, hi = int(FW * 0.30), int(FW * 0.70)
            for c in range(lo, hi):
                hit = sum(1 for y in range(FH) if abs(raw[y * FW + c] - raw[y * FW + c - 1]) >= TH)
                if hit >= 0.65 * FH:
                    out[c] = hit
        else:
            lo, hi = int(FH * 0.25), int(FH * 0.75)
            for rr in range(lo, hi):
                hit = sum(1 for x in range(FW) if abs(raw[rr * FW + x] - raw[(rr - 1) * FW + x]) >= TH)
                if hit >= 0.65 * FW:
                    out[rr] = hit
        return out

    def spread(raw, axis, pos):
        """Que cada lado tenga contenido (no sea un fondo liso)."""
        vals = []
        if axis == "v":
            for x0, x1 in ((0, pos), (pos, FW)):
                px = [raw[y * FW + x] for y in range(0, FH, 3) for x in range(x0, x1, 3)]
                vals.append(statistics.pstdev(px) if len(px) > 1 else 0)
        else:
            for y0, y1 in ((0, pos), (pos, FH)):
                px = [raw[y * FW + x] for y in range(y0, y1, 3) for x in range(0, FW, 3)]
                vals.append(statistics.pstdev(px) if len(px) > 1 else 0)
        return min(vals)

    for axis in ("v", "h"):
        per = [seams(raw, axis) for raw in fr]
        votes = {}
        for d in per:
            for c in d:
                votes[c] = votes.get(c, 0) + 1
        if not votes:
            continue
        # sumo los vecinos (+-1) para tolerar compresion
        score = {c: votes.get(c - 1, 0) + votes.get(c, 0) + votes.get(c + 1, 0) for c in votes}
        best = max(score, key=lambda c: score[c])
        # una costura de verdad es UNA sola linea; varias lineas rectas = franjas/patron/interfaz, no pantalla doble
        distinct = []
        for c in sorted(votes):
            if votes[c] >= 2 and (not distinct or c - distinct[-1] > 3):
                distinct.append(c)
        if len(distinct) > 1:
            continue
        frames_with = sum(1 for d in per if any(abs(c - best) <= 1 for c in d))
        if frames_with < math.ceil(0.8 * len(fr)):
            continue
        if min(spread(raw, axis, best) for raw in fr) < 6:
            continue
        size = FW if axis == "v" else FH
        return {"axis": axis, "pos": round(best / float(size), 4)}
    return None


def resolve_auto_layout(job, sub, src, ss, dur, sw, sh, force_dual=False):
    """Elige solo el mejor diseno: video ya vertical, pantalla doble, camara pequena encontrada, o pantalla completa."""
    if force_dual:
        try:
            d = detect_dual_screen(job["dir"] / src, ss, dur, sw, sh)
        except Exception:
            d = None
        if d:
            return "dual", d
        sub["log"].append("No encontré dos pantallas en este clip → pantalla completa.")
        return "fill", None
    if sh >= sw * 1.2:
        sub["log"].append("Diseño inteligente: el video ya es vertical → pantalla completa.")
        return "fill", None
    try:
        d = detect_dual_screen(job["dir"] / src, ss, dur, sw, sh)
    except Exception as e:
        d = None
        sub["log"].append(f"No pude revisar si es pantalla doble: {str(e)[:80]}")
    if d:
        sub["log"].append("Diseño inteligente: detecté pantalla doble → apilo las dos pantallas.")
        return "dual", d
    fc = job.get("facecam")
    # solo confío en la cámara marcada por IA o por ti (la automática por color de piel se equivoca)
    if job.get("facecam_src") in ("ia", "manual") and fc:
        if fc.get("w", 0) * fc.get("h", 0) > 0.42:
            sub["log"].append("Diseño inteligente: tu cámara ocupa casi todo el video → pantalla completa.")
            return "fill", None
        sub["log"].append("Diseño inteligente: encontré tu cámara → cámara + gameplay.")
        return "split", None
    sub["log"].append("Diseño inteligente: no hay cámara confiable ni pantalla doble → pantalla completa.")
    return "fill", None


def render_clip(job, sub, item, s, fc):
    jd = job["dir"]
    n = item["n"]
    start, end = float(item["start"]), float(item["end"])
    dur = max(3.0, end - start)
    layout = item.get("layout") if item.get("layout") in LAYOUTS else s["layout"]
    cx_ = clamp(item.get("cx"), 0, 1, 0.5)
    cy_ = clamp(item.get("cy"), 0, 1, 0.5)
    zoom_ = clamp(item.get("zoom"), 1, 4, 1.0)
    show_title = item.get("title_on") if item.get("title_on") is not None else s["titles"]
    show_title = bool(show_title) and bool(item.get("title"))
    W, H = out_dims(layout, s["resolution"])
    fps = int(s["fps"]) if s["fps"] != "original" else int(min(60, max(24, round(job["meta"]["fps"]))))
    pad = 3.0
    rel_peak = item.get("t_peak")
    rel_peak = (float(rel_peak) - start) if rel_peak is not None else dur * 0.6
    rel_peak = min(max(rel_peak, 0.8), max(0.8, dur - 0.8))
    font = find_font()

    # ---- fuente del clip
    src, ss, sw, sh, has_audio = None, start, job["meta"]["width"], job["meta"]["height"], job["has_audio"]
    if job["params"]["url"]:
        setp(sub, 3, "Descargando el clip en alta calidad…")
        a_abs = max(0.0, job["base_offset"] + start - pad)
        z = download_clip_source(job, a_abs, job["base_offset"] + end + pad, n, 2160 if int(s["resolution"]) >= 1080 else 1080)
        if z:
            info = probe(jd / z)
            src, ss, sw, sh, has_audio = z, job["base_offset"] + start - a_abs, info["width"], info["height"], info["has_audio"]
        else:
            sub["log"].append("No pude bajar la calidad alta; uso la calidad de análisis (baja).")
    if src is None:
        if job["params"].get("file_name"):
            src = job["orig"]
            sw, sh = job["orig_info"]["width"], job["orig_info"]["height"]
        else:
            src = job["low"]

    # ---- diseno inteligente
    dual = None
    if layout in ("auto", "dual"):
        layout, dual = resolve_auto_layout(job, sub, src, ss, dur, sw, sh, force_dual=(layout == "dual"))

    # ---- seguir la accion (solo recorte del gameplay)
    gx_expr = None
    if s["follow_action"] and ((s["game_fit"] == "crop" and layout in ("split", "circle", "game")) or layout == "fill"):
        setp(sub, 8, "Siguiendo la acción…")
        try:
            if layout == "split":
                Hc = even(H * s["split_pct"] / 100)
                rw, rh = W, H - Hc
            else:
                rw, rh = W, H
            pts = motion_track(jd / src, ss, dur, rw, rh, sw, sh, fc if layout not in ("game", "fill") else None)
            if pts:
                gx_expr = pl_expr(pts)
        except Exception as e:
            sub["log"].append(f"No pude seguir la acción: {str(e)[:80]}")
    gx_val = gx_expr if gx_expr else f"{clamp(s['game_x'], 0, 100, 50) / 100.0:.3f}"
    fill_x = gx_expr if (gx_expr and layout == "fill") else f"{cx_:.3f}"

    # ---- subtitulos (transcripcion)
    cap = None
    cap_raw = None
    mute_r = []
    edited = item.get("cap_lines") or []
    need_tr = (s["captions"] and not edited) or s["mute_profanity"]
    if need_tr and not get_key("openai_key"):
        if s["mute_profanity"]:
            sub["log"].append("No pude tapar groserías: falta la clave de OpenAI (Ajustes).")
    elif need_tr:
        try:
            setp(sub, 12, "Escuchando el clip (subtítulos / groserías)…")
            capf = f"cap_{n}.mp3"
            run_ffmpeg(sub, ["-ss", f"{ss:.2f}", "-t", f"{dur:.2f}", "-i", src, "-vn", "-ac", "1", "-ar", "16000",
                             "-b:a", "48k", capf], f"cap{n}")
            cap_raw = whisper(jd / capf, verbose=True)
        except Cancelled:
            raise
        except Exception as e:
            sub["log"].append(f"No pude transcribir el clip: {str(e)[:120]}")
    if s["mute_profanity"] and cap_raw:
        mute_r = profane_ranges(cap_raw.get("words") or [], dur)
        sub["log"].append(f"Tapé {len(mute_r)} grosería(s)." if mute_r else "No encontré groserías en este clip.")
    if edited and s["captions"]:
        ew = []
        for ln in edited[:80]:
            try:
                a, b, tx = float(ln[0]), float(ln[1]), str(ln[2]).strip()
            except Exception:
                continue
            toks = tx.split()
            if not toks or b <= a:
                continue
            step = (b - a) / len(toks)
            ew += [{"word": t, "start": a + k * step, "end": a + (k + 1) * step} for k, t in enumerate(toks)]
        cap = {"words": ew} if ew else None
    elif s["captions"] and cap_raw:
        cap = cap_raw
    if cap and s["mute_profanity"] and cap.get("words"):
        cap = dict(cap, words=[dict(w, word=censor_text(w.get("word", ""))) for w in cap["words"]])

    sfx = None
    if s["sfx"] != "none":
        try:
            sfx = sfx_asset(s["sfx"])
        except Exception as e:
            sub["log"].append(f"No pude crear el efecto de sonido: {str(e)[:80]}")
    music = asset_path(s["music"]) if s["music"] else None
    logo = asset_path(s["logo"]) if s["logo"] else None
    crf = {"alta": 16, "media": 22, "baja": 28}.get(s["quality"], 23)
    cx, cy, cw, ch = cam_rect_px(fc, sw, sh)
    camcrop = f"crop={cw}:{ch}:{cx}:{cy}"
    fit = s["game_fit"]
    main_name = f"main_{n}.mp4"

    def build(mode):
        """mode: 'ass' (subtitulos animados) | 'simple' (drawtext) | 'none' (sin textos)."""
        inputs = ["-ss", f"{ss:.3f}", "-t", f"{dur:.3f}", "-i", src]
        idx = [1]

        def add_in(args):
            inputs.extend(args)
            idx[0] += 1
            return idx[0] - 1

        parts = []
        if layout == "horizontal":
            parts.append(f"[0:v]scale={W}:{H}:force_original_aspect_ratio=decrease,pad={W}:{H}:(ow-iw)/2:(oh-ih)/2:color=black[vb]")
        elif layout == "cam":
            parts.append(f"[0:v]{camcrop},scale={W}:{H}:force_original_aspect_ratio=increase,crop={W}:{H}[vb]")
        elif layout == "game":
            parts.append(game_region("0:v", "vb", W, H, fit, gx_val))
        elif layout == "fill":
            sc = max(W / float(sw), H / float(sh)) * zoom_
            sw2, sh2 = max(W, even(sw * sc)), max(H, even(sh * sc))
            parts.append(f"[0:v]scale={sw2}:{sh2},crop={W}:{H}:x='(iw-ow)*({fill_x})':y='(ih-oh)*{cy_:.3f}'[vb]")
        elif layout == "dual":
            m = 0.012
            if dual["axis"] == "v":
                Ht = even(H / 2)
                Hb = H - Ht
                lw = even(sw * max(0.2, dual["pos"] - m))
                rx = even(sw * min(0.8, dual["pos"] + m))
                rw = max(2, even(sw - rx))
                parts += ["[0:v]split=2[da][db]",
                          f"[da]crop={lw}:{even(sh)}:0:0,scale={W}:{Ht}:force_original_aspect_ratio=increase,crop={W}:{Ht}[dt]",
                          f"[db]crop={rw}:{even(sh)}:{rx}:0,scale={W}:{Hb}:force_original_aspect_ratio=increase,crop={W}:{Hb}[dm]",
                          "[dt][dm]vstack=inputs=2[vb]"]
            else:
                share = min(0.65, max(0.35, dual["pos"]))
                Ht = even(H * share)
                Hb = H - Ht
                th = even(sh * max(0.2, dual["pos"] - m))
                ry = even(sh * min(0.8, dual["pos"] + m))
                bh = max(2, even(sh - ry))
                parts += ["[0:v]split=2[da][db]",
                          f"[da]crop={even(sw)}:{th}:0:0,scale={W}:{Ht}:force_original_aspect_ratio=increase,crop={W}:{Ht}[dt]",
                          f"[db]crop={even(sw)}:{bh}:0:{ry},scale={W}:{Hb}:force_original_aspect_ratio=increase,crop={W}:{Hb}[dm]",
                          "[dt][dm]vstack=inputs=2[vb]"]
        elif layout == "split":
            Hc = even(H * s["split_pct"] / 100)
            Hg = H - Hc
            parts += ["[0:v]split=2[gs][cs]", game_region("gs", "gv", W, Hg, fit, gx_val),
                      f"[cs]{camcrop},scale={W}:{Hc}:force_original_aspect_ratio=increase,crop={W}:{Hc}[cv]"]
            parts.append("[cv][gv]vstack=inputs=2[vb]" if s["cam_order"] == "top" else "[gv][cv]vstack=inputs=2[vb]")
        else:  # circle
            D = even(W * 0.40)
            mask, ring = make_circle_assets(job, D)
            m = int(W * 0.04)
            pos = s["circle_pos"]
            X = {"bl": m, "tl": m, "br": W - D - m, "tr": W - D - m, "bc": (W - D) // 2}[pos]
            Y = int(H * 0.12) if pos in ("tl", "tr") else H - D - int(H * 0.14)
            sq = min(cw, ch)
            mi = add_in(["-loop", "1", "-i", mask])
            ri = add_in(["-loop", "1", "-i", ring])
            parts += ["[0:v]split=2[gs][cs]", game_region("gs", "gbase", W, H, fit, gx_val),
                      f"[cs]crop={sq}:{sq}:{cx + (cw - sq) // 2}:{cy + (ch - sq) // 2},scale={D}:{D},format=yuva420p[sq]",
                      f"[sq][{mi}:v]alphamerge[cc]", f"[gbase][cc]overlay={X}:{Y}[t1]",
                      f"[t1][{ri}:v]overlay={X}:{Y}:shortest=1[vb]"]
        cur = "vb"
        bgc = item.get("bg") or {}
        if bgc.get("mode") == "chroma":
            parts.append(f"[{cur}]format=rgba,chromakey=0x{bgc['color']}:{bgc['sim']}:0.1[ck]")
            bap = asset_path(bgc.get("bgimg") or "") if bgc.get("back") == "image" else None
            if bap:
                bi = add_in(["-loop", "1", "-i", str(bap)])
                parts.append(f"[{bi}:v]scale={W}:{H}:force_original_aspect_ratio=increase,crop={W}:{H},format=rgba[bgp]")
            else:
                bi = add_in(["-f", "lavfi", "-t", f"{dur:.2f}", "-i", f"color=c=0x{bgc['bgcolor']}:s={W}x{H}:r=30"])
                parts.append(f"[{bi}:v]format=rgba[bgp]")
            parts.append("[bgp][ck]overlay=shortest=1,format=yuv420p[vbg]")
            cur = "vbg"
        if s["zoom_peak"] and layout != "horizontal":
            z = f"if(gte(t,{rel_peak:.2f}),0.12*exp(-5*(t-{rel_peak:.2f})),0)"
            parts.append(f"[{cur}]scale=w='trunc({W}*(1+{z})/2)*2':h='trunc({H}*(1+{z})/2)*2':eval=frame,crop={W}:{H}[vz]")
            cur = "vz"
        if logo:
            li = add_in(["-i", str(logo)])
            lw = int(W * 0.16)
            mg = int(W * 0.03)
            lx = f"{mg}" if s["logo_pos"] in ("tl", "bl") else f"W-w-{mg}"
            ly = f"{mg}" if s["logo_pos"] in ("tl", "tr") else f"H-h-{mg}"
            parts.append(f"[{li}:v]scale={lw}:-1,format=rgba,colorchannelmixer=aa=0.9[lg]")
            parts.append(f"[{cur}][lg]overlay={lx}:{ly}[vl]")
            cur = "vl"
        ovs = sanitize_overlays(list(s.get("overlays") or []) + list(item.get("overlays") or []))
        for ov in ovs:
            if ov["type"] != "image":
                continue
            ap = asset_path(ov["asset"])
            if not ap:
                continue
            oi = add_in(["-loop", "1", "-i", str(ap)])
            ow = max(16, even(W * ov["size"]))
            t1 = ov["t1"] if ov["t1"] >= 0 else dur
            nm = f"oi{oi}"
            parts.append(f"[{oi}:v]scale={ow}:-2,format=rgba[{nm}]")
            parts.append(f"[{cur}][{nm}]overlay=x='max(0,min(W-w,W*{ov['x']}-w/2))':y='max(0,min(H-h,H*{ov['y']}-h/2))':"
                         f"enable='between(t,{ov['t0']:.2f},{t1:.2f})':shortest=1[ovo{oi}]")
            cur = f"ovo{oi}"
        post = []
        if mode != "none":
            for k2, ov in enumerate(ovs):
                if ov["type"] != "text":
                    continue
                t1 = ov["t1"] if ov["t1"] >= 0 else dur
                xe = f"max(8\\,min(w-text_w-8\\,w*{ov['x']}-text_w/2))"
                ye = f"max(8\\,min(h-text_h-8\\,h*{ov['y']}-text_h/2))"
                fs2 = max(14, int(W * ov["size"]))
                post.append(drawtext(jd, f"ov_{n}_{k2}", ov["text"], fs2, ov["color"], ye, ov["t0"], max(ov["t0"] + 0.5, t1), W,
                                     font, box=(ov["bg"] == "box"), fade=False, card=(ov["bg"] == "card"), x_expr=xe))
            if show_title:
                ty = "h*0.15" if any(o["type"] == "text" and o["y"] < 0.15 for o in ovs) else "h*0.07"
                post.append(drawtext(jd, f"title_{n}", item["title"], int(W * 0.052), "111111", ty, 0.2,
                                     min(5.0, dur), W, font, card=True))
            if cap:
                if mode == "ass":
                    fam = ttf_family(font) if font else None
                    if fam and make_ass(jd / f"cap_{n}.ass", cap, W, H, fam, dur):
                        (jd / "fonts").mkdir(exist_ok=True)
                        shutil.copy(font, jd / "fonts" / Path(font).name)
                        post.append(f"subtitles=filename=cap_{n}.ass:fontsdir=fonts")
                    else:
                        mode = "simple"
                if mode == "simple":
                    for k, (a, b, t) in enumerate(caption_items(cap, dur)):
                        post.append(drawtext(jd, f"cap_{n}_{k}", t, int(W * 0.066), "ffe600", "h*0.68", a, b, W, font,
                                             upper=True, fade=False))
        post += [f"fps={fps}", "setsar=1", "format=yuv420p"]
        parts.append(f"[{cur}]{','.join(post)}[vout]")

        # ---- audio
        if has_audio:
            af = "aresample=44100,aformat=sample_fmts=fltp:channel_layouts=stereo"
            if s["normalize"]:
                af += ",loudnorm=I=-16:TP=-1.5:LRA=11"
            for (ma, mb) in mute_r:   # silencia SOLO la palabra (de su inicio a su final)
                af += f",volume=enable='between(t,{ma:.2f},{mb:.2f})':volume=0"
            beep = s.get("profanity_sound") in ("beep", "low") and mute_r
            if beep:
                bi = add_in(["-f", "lavfi", "-t", f"{dur:.2f}", "-i", f"sine=frequency={1000 if s['profanity_sound'] == 'beep' else 400}:sample_rate=44100"])
                ex = "+".join(f"between(t,{ma:.2f},{mb:.2f})" for ma, mb in mute_r)
                parts.append(f"[0:a]{af}[a0m]")
                parts.append(f"[{bi}:a]aformat=sample_fmts=fltp:channel_layouts=stereo,volume='0.3*({ex})':eval=frame[bp]")
                parts.append("[a0m][bp]amix=inputs=2:duration=first:normalize=0[a0]")
            else:
                parts.append(f"[0:a]{af}[a0]")
        else:
            si = add_in(["-f", "lavfi", "-t", f"{dur:.2f}", "-i", "anullsrc=r=44100:cl=stereo"])
            parts.append(f"[{si}:a]aformat=sample_fmts=fltp:channel_layouts=stereo[a0]")
        ca = "a0"
        if sfx:
            xi = add_in(["-i", str(sfx)])
            d = int(max(0.0, rel_peak - 0.15) * 1000)
            parts.append(f"[{xi}:a]adelay={d}|{d},volume=0.8[sx]")
            parts.append(f"[{ca}][sx]amix=inputs=2:duration=first:normalize=0[a1]")
            ca = "a1"
        if music:
            mi2 = add_in(["-stream_loop", "-1", "-i", str(music)])
            parts.append(f"[{mi2}:a]aresample=44100,aformat=sample_fmts=fltp:channel_layouts=stereo,"
                         f"volume={s['music_volume']:.3f}[mus]")
            if s["music_duck"]:
                parts.append(f"[{ca}]asplit=2[vm][vk]")
                parts.append("[mus][vk]sidechaincompress=threshold=0.03:ratio=10:attack=15:release=400[md]")
                parts.append("[vm][md]amix=inputs=2:duration=first:normalize=0[a2]")
            else:
                parts.append(f"[{ca}][mus]amix=inputs=2:duration=first:normalize=0[a2]")
            ca = "a2"
        parts.append(f"[{ca}]afade=t=in:st=0:d=0.12,afade=t=out:st={max(0.0, dur - 0.25):.2f}:d=0.25[aout]")
        args = inputs + ["-filter_complex", ";".join(parts), "-map", "[vout]", "-map", "[aout]", "-t", f"{dur:.3f}",
                         "-c:v", "libx264", "-preset", "veryfast", "-crf", str(crf), "-pix_fmt", "yuv420p", "-r", str(fps),
                         "-c:a", "aac", "-b:a", "160k", "-movflags", "+faststart", main_name]
        return args

    setp(sub, 20, "Renderizando…")
    wants_text = bool(cap) or show_title
    modes = (["ass", "simple", "none"] if cap else ["simple", "none"]) if wants_text else ["none"]
    last_err = None
    for k, mode in enumerate(modes):
        try:
            run_ffmpeg(sub, build(mode), f"clip{n}{mode}", total=dur, p0=20, p1=94)
            if k > 0:
                sub["log"].append({"simple": "Los subtítulos animados fallaron; usé subtítulos simples.",
                                   "none": "No pude dibujar textos (¿falta una fuente?); el clip salió sin textos."}[mode])
            last_err = None
            break
        except Cancelled:
            raise
        except RuntimeError as e:
            last_err = e
    if last_err:
        raise last_err

    # ---- intro / final con texto
    out = f"clip_{n}_{uuid.uuid4().hex[:5]}.mp4"
    if s["intro_text"] or s["outro_text"]:
        setp(sub, 95, "Agregando intro/final…")
        files, args = [], []
        if s["intro_text"]:
            files.append(render_card(sub, f"intro{n}", s["intro_text"], W, H, fps, font))
        files.append(main_name)
        if s["outro_text"]:
            files.append(render_card(sub, f"outro{n}", s["outro_text"], W, H, fps, font))
        for f in files:
            args += ["-i", f]
        ins = "".join(f"[{i}:v][{i}:a]" for i in range(len(files)))
        g = "".join(f"[{i}:v]fps={fps},setsar=1,format=yuv420p[v{i}];[{i}:a]aresample=44100,aformat=sample_fmts=fltp:"
                    f"channel_layouts=stereo[a{i}];" for i in range(len(files)))
        ins = "".join(f"[v{i}][a{i}]" for i in range(len(files)))
        args += ["-filter_complex", f"{g}{ins}concat=n={len(files)}:v=1:a=1[v][a]", "-map", "[v]", "-map", "[a]",
                 "-c:v", "libx264", "-preset", "veryfast", "-crf", str(crf), "-pix_fmt", "yuv420p", "-c:a", "aac",
                 "-b:a", "160k", "-movflags", "+faststart", out]
        run_ffmpeg(sub, args, f"cards{n}")
    else:
        os.replace(jd / main_name, jd / out)
    for f in (list(jd.glob(f"clipsrc_{n}.*")) + list(jd.glob(f"cap_{n}*")) + list(jd.glob(f"title_{n}.txt")) +
              list(jd.glob(f"intro{n}*")) + list(jd.glob(f"outro{n}*")) + list(jd.glob(f"main_{n}.mp4"))):
        try:
            f.unlink()
        except Exception:
            pass
    return out


# ---------------------------------------------------------------- cola de render
RENDER_SEM = threading.Semaphore(1)


def clip_by_i(job, i):
    return next((c for c in job["clips"] if c.get("i") == i), None)


def start_export(job, items, settings):
    """items: [{i, start, end, title, layout}]. Devuelve la lista de numeros de export creados."""
    s = sanitize_settings(settings, job.get("settings"))
    work, ns = [], []
    for it in items:
        c = clip_by_i(job, it.get("i"))
        n = job["next_export"]
        job["next_export"] += 1
        sub = {"dir": job["dir"], "n": n, "i": it.get("i"), "status": "queued", "progress": 0, "stage": "En cola", "log": [],
               "file": None, "error": None, "cancel": False, "proc": None, "title": str(it.get("title", ""))[:70],
               "layout": it.get("layout") or s["layout"], "created": now(), "dur": 0}
        job["exports"].append(sub)
        work.append((dict(it, n=n, t_peak=c.get("t_peak") if c else None), sub))
        ns.append(n)
    threading.Thread(target=export_worker, args=(job, work, s), daemon=True).start()
    return ns


def prune_exports(job, i, keep_n):
    busy = {(t["job"], t.get("export")) for t in QUEUE if t["status"] in ("pending", "running")}
    for e in list(job["exports"]):
        if e.get("i") == i and e["n"] != keep_n and e["status"] in ("done", "error", "cancelled") \
                and (job["id"], e["n"]) not in busy:
            if e.get("file"):
                try:
                    (job["dir"] / e["file"]).unlink()
                except Exception:
                    pass
            job["exports"].remove(e)


def export_worker(job, work, s):
    with RENDER_SEM:
        for it, sub in work:
            if sub.get("cancel") or job["id"] not in JOBS:
                sub["status"] = "cancelled"
                continue
            try:
                sub["status"] = "running"
                sub["t_start"] = now()
                sub["stage"] = "Empezando…"
                fc = job.get("facecam") or default_cam()
                sub["file"] = render_clip(job, sub, it, s, fc)
                try:
                    sub["dur"] = round(probe(job["dir"] / sub["file"])["duration"], 1)
                except Exception:
                    pass
                sub["status"] = "done"
                setp(sub, 100, "Listo")
                prune_exports(job, sub["i"], sub["n"])
            except Cancelled:
                sub["status"] = "cancelled"
            except Exception as e:
                sub["status"] = "error"
                sub["error"] = str(e)[:400]
                sub["log"].append("Error: " + str(e)[:300])
            save_job(job)


# ---------------------------------------------------------------- redes: cuentas, cola y programacion
QUEUE = []
Q_LOCK = threading.RLock()
TASK_SEM = threading.Semaphore(2)
FB_SCOPES = "pages_show_list,pages_manage_posts,pages_read_engagement,publish_video"
TT_SCOPES = "user.info.basic,video.publish,video.upload"
RETRY_WAIT = int(os.environ.get("CH_RETRY_WAIT", 120))
MAX_TRIES = 3
PENDING = ("pending", "running")


def save_queue():
    with Q_LOCK:
        try:
            tmp = QUEUE_FILE.with_suffix(".tmp")
            tmp.write_text(json.dumps(QUEUE, default=str), encoding="utf-8")
            os.replace(tmp, QUEUE_FILE)
        except Exception:
            pass


def load_queue():
    try:
        data = json.loads(QUEUE_FILE.read_text(encoding="utf-8"))
    except Exception:
        data = []
    for t in data:
        if t.get("status") == "running":
            t["status"] = "pending"
        QUEUE.append(t)
    return len(QUEUE)


def hashtag_line(tags):
    out = []
    for t in tags or []:
        t = re.sub(r"[^\w]", "", str(t).lstrip("#"), flags=re.UNICODE)
        if t and ("#" + t) not in out:
            out.append("#" + t)
    return " ".join(out[:15])


def full_text(task, limit):
    cap = (task.get("caption") or "").strip()
    tags = hashtag_line(task.get("hashtags"))
    txt = (cap + ("\n\n" if cap and tags else "") + tags).strip()
    return txt[:limit]


def mask(s):
    s = s or ""
    return (s[:4] + "…" + s[-3:]) if len(s) > 10 else ("•" * len(s))


def accounts_view():
    fb, tt = account("facebook"), account("tiktok")
    fb_pages = [{"id": p["id"], "name": p.get("name", "")} for p in fb.get("pages", [])]
    return {
        "facebook": {"app_id": fb.get("app_id", ""), "has_secret": bool(fb.get("app_secret")),
                     "connected": bool(fb.get("page_id") and fb.get("page_token")), "page_id": fb.get("page_id", ""),
                     "page_name": fb.get("page_name", ""), "pages": fb_pages,
                     "redirect": f"http://localhost:{PORT}/api/fb/callback"},
        "tiktok": {"client_key": tt.get("client_key", ""), "has_secret": bool(tt.get("client_secret")),
                   "redirect_uri": tt.get("redirect_uri", ""), "connected": bool(tt.get("access_token")),
                   "name": tt.get("display_name") or tt.get("open_id", ""),
                   "expires": tt.get("expires_at", 0), "refresh_ok": bool(tt.get("refresh_token"))},
    }


# ---------------------------------------------------------------- Facebook
def fb_login_url():
    a = account("facebook")
    if not a.get("app_id") or not a.get("app_secret"):
        raise RuntimeError("Primero guarda el ID y la clave secreta de tu app de Facebook.")
    state = uuid.uuid4().hex
    a["state"] = state
    set_account("facebook", a)
    q = urllib.parse.urlencode({"client_id": a["app_id"], "redirect_uri": f"http://localhost:{PORT}/api/fb/callback",
                                "scope": FB_SCOPES, "state": state, "response_type": "code"})
    return f"{FB_DIALOG}?{q}"


def fb_finish_login(code, state):
    a = account("facebook")
    if not a.get("state") or state != a["state"]:
        raise RuntimeError("La respuesta de Facebook no coincide con el intento de conexión. Vuelve a intentarlo.")
    redirect = f"http://localhost:{PORT}/api/fb/callback"
    st, j = http_json("GET", f"{FB_GRAPH}/oauth/access_token?" + urllib.parse.urlencode(
        {"client_id": a["app_id"], "client_secret": a["app_secret"], "redirect_uri": redirect, "code": code}))
    if st != 200 or "access_token" not in j:
        raise RuntimeError("Facebook rechazó el código: " + fb_err(j))
    st, j2 = http_json("GET", f"{FB_GRAPH}/oauth/access_token?" + urllib.parse.urlencode(
        {"grant_type": "fb_exchange_token", "client_id": a["app_id"], "client_secret": a["app_secret"],
         "fb_exchange_token": j["access_token"]}))
    user_token = j2.get("access_token") or j["access_token"]
    st, pj = http_json("GET", f"{FB_GRAPH}/me/accounts?" + urllib.parse.urlencode(
        {"access_token": user_token, "fields": "id,name,access_token", "limit": 50}))
    if st != 200:
        raise RuntimeError("No pude leer tus páginas: " + fb_err(pj))
    pages = [{"id": p["id"], "name": p.get("name", ""), "token": p.get("access_token", "")} for p in pj.get("data", [])]
    if not pages:
        raise RuntimeError("Tu cuenta no administra ninguna página de Facebook (los Reels se publican en páginas).")
    a.pop("state", None)
    a["pages"] = pages
    a["page_id"], a["page_name"], a["page_token"] = pages[0]["id"], pages[0]["name"], pages[0]["token"]
    set_account("facebook", a)
    return pages


def fb_select_page(pid):
    a = account("facebook")
    p = next((x for x in a.get("pages", []) if x["id"] == pid), None)
    if not p:
        raise RuntimeError("Esa página no está en tu lista.")
    a["page_id"], a["page_name"], a["page_token"] = p["id"], p["name"], p["token"]
    set_account("facebook", a)


def fb_manual(page_id, token):
    page_id, token = (page_id or "").strip(), (token or "").strip()
    if not page_id or not token:
        raise RuntimeError("Pon el ID de la página y su token.")
    st, j = http_json("GET", f"{FB_GRAPH}/{page_id}?" + urllib.parse.urlencode({"fields": "id,name", "access_token": token}))
    if st != 200:
        raise RuntimeError("Facebook no aceptó ese token/ID: " + fb_err(j))
    a = account("facebook")
    a["page_id"], a["page_name"], a["page_token"] = j.get("id", page_id), j.get("name", ""), token
    a.setdefault("pages", [])
    if not any(p["id"] == a["page_id"] for p in a["pages"]):
        a["pages"].append({"id": a["page_id"], "name": a["page_name"], "token": token})
    set_account("facebook", a)


def fb_err(j):
    e = (j or {}).get("error")
    if isinstance(e, dict):
        return f"{e.get('message', '')} (código {e.get('code', '?')})"[:250]
    return str(j)[:250]


def send_bytes(method, url, headers, data, timeout=600):
    req = urllib.request.Request(url, data=data, headers=headers, method=method)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return r.status, r.read().decode(errors="ignore")
    except urllib.error.HTTPError as e:
        return e.code, e.read().decode(errors="ignore")
    except urllib.error.URLError as e:
        raise RuntimeError(f"No pude subir el archivo: {e.reason}")


def post_facebook(task, path):
    a = account("facebook")
    if not (a.get("page_id") and a.get("page_token")):
        raise PermanentError("Facebook no está conectado (pestaña Cuentas).")
    pid, tok = a["page_id"], a["page_token"]
    size = path.stat().st_size
    st, j = http_json("POST", f"{FB_GRAPH}/{pid}/video_reels", json_body={"upload_phase": "start", "access_token": tok})
    if st != 200 or "video_id" not in j:
        raise PermanentError("Facebook no empezó la subida: " + fb_err(j))
    vid = j["video_id"]
    up = j.get("upload_url") or f"{FB_RUPLOAD}/{vid}"
    task["stage"] = "Subiendo a Facebook…"
    st, body = send_bytes("POST", up, {"Authorization": f"OAuth {tok}", "offset": "0", "file_size": str(size),
                                       "Content-Type": "application/octet-stream"}, path.read_bytes())
    if st != 200:
        raise RuntimeError(f"La subida a Facebook falló ({st}): {body[:200]}")
    fin = {"upload_phase": "finish", "video_id": vid, "access_token": tok, "description": full_text(task, 2200),
           "video_state": "PUBLISHED"}
    native = bool(task.get("native"))
    if native:
        fin["video_state"] = "SCHEDULED"
        fin["scheduled_publish_time"] = int(task["when"])
    st, j = http_json("POST", f"{FB_GRAPH}/{pid}/video_reels", json_body=fin)
    if st != 200 or not j.get("success", True):
        raise PermanentError("Facebook no terminó de publicar: " + fb_err(j))
    note = (f"Programado dentro de Facebook para el {fmt_when(task['when'])}" if native else "Publicado en Facebook")
    return {"id": vid, "url": f"https://www.facebook.com/reel/{vid}", "note": note}


# ---------------------------------------------------------------- TikTok
def tt_login_url():
    a = account("tiktok")
    if not a.get("client_key") or not a.get("client_secret") or not a.get("redirect_uri"):
        raise RuntimeError("Guarda primero client key, client secret y redirect URI de tu app de TikTok.")
    state = uuid.uuid4().hex[:16]
    a["state"] = state
    set_account("tiktok", a)
    q = urllib.parse.urlencode({"client_key": a["client_key"], "scope": TT_SCOPES, "response_type": "code",
                                "redirect_uri": a["redirect_uri"], "state": state})
    return f"{TT_AUTH}?{q}"


def tt_store_token(a, j):
    a["access_token"] = j["access_token"]
    a["refresh_token"] = j.get("refresh_token", a.get("refresh_token", ""))
    a["open_id"] = j.get("open_id", a.get("open_id", ""))
    a["expires_at"] = now() + int(j.get("expires_in", 86400)) - 60
    set_account("tiktok", a)


def tt_finish_login(pasted):
    """pasted: la URL completa a la que te mando TikTok (o solo el code)."""
    a = account("tiktok")
    pasted = (pasted or "").strip()
    code = pasted
    if "code=" in pasted:
        q = urllib.parse.parse_qs(urllib.parse.urlparse(pasted).query)
        if not q:
            q = urllib.parse.parse_qs(pasted.split("?", 1)[-1])
        code = (q.get("code") or [""])[0]
        if q.get("error"):
            raise RuntimeError("TikTok devolvió un error: " + (q.get("error_description") or q["error"])[0])
        if a.get("state") and (q.get("state") or [""])[0] != a["state"]:
            raise RuntimeError("El 'state' no coincide. Empieza de nuevo con 'Conectar TikTok'.")
    code = urllib.parse.unquote(code)
    if not code:
        raise RuntimeError("No encontré el 'code' en lo que pegaste.")
    st, j = http_json("POST", f"{TT_BASE}/v2/oauth/token/", form={
        "client_key": a["client_key"], "client_secret": a["client_secret"], "code": code,
        "grant_type": "authorization_code", "redirect_uri": a["redirect_uri"]})
    if st != 200 or "access_token" not in j:
        raise RuntimeError("TikTok rechazó el código: " + str(j.get("error_description") or j)[:250])
    a.pop("state", None)
    tt_store_token(a, j)
    try:
        st, u = http_json("GET", f"{TT_BASE}/v2/user/info/?fields=open_id,display_name",
                          headers={"Authorization": f"Bearer {a['access_token']}"})
        name = ((u.get("data") or {}).get("user") or {}).get("display_name")
        if name:
            a = account("tiktok")
            a["display_name"] = name
            set_account("tiktok", a)
    except Exception:
        pass


def tt_token():
    a = account("tiktok")
    if not a.get("access_token"):
        raise PermanentError("TikTok no está conectado (pestaña Cuentas).")
    if a.get("expires_at", 0) < now() and a.get("refresh_token"):
        st, j = http_json("POST", f"{TT_BASE}/v2/oauth/token/", form={
            "client_key": a["client_key"], "client_secret": a["client_secret"], "grant_type": "refresh_token",
            "refresh_token": a["refresh_token"]})
        if st != 200 or "access_token" not in j:
            raise PermanentError("No pude renovar la sesión de TikTok; vuelve a conectarla. " +
                                 str(j.get("error_description") or j)[:150])
        tt_store_token(a, j)
        a = account("tiktok")
    return a["access_token"]


def tt_api(path, body, tok):
    st, j = http_json("POST", TT_BASE + path, json_body=body,
                      headers={"Authorization": f"Bearer {tok}"})
    err = j.get("error") or {}
    if st != 200 or (err.get("code") not in (None, "ok")):
        raise RuntimeError(f"TikTok: {err.get('message') or j}"[:300] + (f" [{err.get('code')}]" if err.get("code") else ""))
    return j.get("data") or {}


def tt_creator_info():
    return tt_api("/v2/post/publish/creator_info/query/", {}, tt_token())


def post_tiktok(task, path):
    tok = tt_token()
    size = path.stat().st_size
    draft = task.get("tt_mode") == "draft"
    if size <= TT_CHUNK:
        chunk, total = size, 1
    else:
        chunk = TT_CHUNK
        total = size // chunk
    src = {"source": "FILE_UPLOAD", "video_size": size, "chunk_size": chunk, "total_chunk_count": total}
    if draft:
        init = tt_api("/v2/post/publish/inbox/video/init/", {"source_info": src}, tok)
    else:
        info = tt_creator_info()
        opts = info.get("privacy_level_options") or ["SELF_ONLY"]
        want = task.get("privacy") or "SELF_ONLY"
        if want not in opts:
            want = opts[0] if "SELF_ONLY" not in opts else "SELF_ONLY"
        mx = info.get("max_video_post_duration_sec")
        try:
            d = probe(path)["duration"]
            if mx and d > mx:
                raise PermanentError(f"Tu cuenta de TikTok solo permite videos de hasta {mx} s y este dura {d:.0f} s.")
        except PermanentError:
            raise
        except Exception:
            pass
        init = tt_api("/v2/post/publish/video/init/", {
            "post_info": {"title": full_text(task, 2200), "privacy_level": want, "disable_duet": False,
                          "disable_comment": False, "disable_stitch": False},
            "source_info": src}, tok)
        task["privacy_used"] = want
    up, pub = init.get("upload_url"), init.get("publish_id")
    if not up or not pub:
        raise RuntimeError("TikTok no dio la dirección de subida.")
    task["stage"] = "Subiendo a TikTok…"
    with open(path, "rb") as f:
        for k in range(total):
            a0 = k * chunk
            ln = chunk if k < total - 1 else size - a0
            f.seek(a0)
            data = f.read(ln)
            st, body = send_bytes("PUT", up, {"Content-Type": "video/mp4", "Content-Length": str(ln),
                                      "Content-Range": f"bytes {a0}-{a0 + ln - 1}/{size}"}, data)
            if st not in (200, 201, 206):
                raise RuntimeError(f"La subida a TikTok falló en el trozo {k + 1}/{total} ({st}): {body[:150]}")
            task["progress"] = int(100 * (k + 1) / total)
    status = "PROCESSING"
    for _ in range(12):
        try:
            sd = tt_api("/v2/post/publish/status/fetch/", {"publish_id": pub}, tok)
            status = sd.get("status", status)
            if status in ("PUBLISH_COMPLETE", "SEND_TO_USER_INBOX", "FAILED"):
                if status == "FAILED":
                    raise PermanentError("TikTok no aceptó el video: " + str(sd.get("fail_reason", "motivo desconocido")))
                break
        except PermanentError:
            raise
        except Exception:
            pass
        time.sleep(float(os.environ.get("CH_POLL", 4)))
    if draft:
        note = "Enviado a tu bandeja de TikTok: abre la app, toca la notificación y publícalo."
    elif task.get("privacy_used") == "SELF_ONLY" and task.get("privacy") not in (None, "SELF_ONLY"):
        note = "Subido a TikTok como PRIVADO (tu app aún no está auditada por TikTok, así que no deja publicar en público)."
    else:
        note = "Subido a TikTok" + (" (privado)" if task.get("privacy_used") == "SELF_ONLY" else "")
    if status == "PROCESSING":
        note += " · TikTok sigue procesándolo."
    return {"id": pub, "url": "", "note": note}


# ---------------------------------------------------------------- cola
class PermanentError(Exception):
    pass


def task_file(task):
    job = JOBS.get(task["job"])
    if not job:
        raise PermanentError("El trabajo de este clip ya no existe (se borró).")
    e = next((x for x in job["exports"] if x["n"] == task["export"]), None)
    if not e:
        raise PermanentError("El clip ya no existe (se rehízo o se borró). Vuelve a programarlo.")
    return job, e


def validate_publish(platform, tt_mode="direct"):
    if platform == "facebook":
        a = account("facebook")
        if not (a.get("page_id") and a.get("page_token")):
            return "Conecta primero tu página de Facebook en la pestaña Cuentas."
    elif platform == "tiktok":
        if not account("tiktok").get("access_token"):
            return "Conecta primero TikTok en la pestaña Cuentas."
    else:
        return "Red no válida."
    return None


def add_tasks(specs):
    """specs: [{job, export, platform, caption, hashtags, when(ts|None), privacy, tt_mode}] -> (tareas, errores)."""
    made, errs = [], []
    for sp in specs:
        platform = sp.get("platform")
        msg = validate_publish(platform)
        job = JOBS.get(sp.get("job"))
        e = next((x for x in (job or {}).get("exports", []) if x["n"] == sp.get("export")), None)
        if not msg and not e:
            msg = "Ese clip no existe."
        if not msg and e["status"] not in ("done", "queued", "running"):
            msg = "Ese clip no está listo (rehazlo primero)."
        when = sp.get("when")
        if not msg and when:
            try:
                when = float(when)
            except Exception:
                msg = "Fecha no válida."
        if msg:
            errs.append({"platform": platform, "export": sp.get("export"), "error": msg})
            continue
        t = {"id": uuid.uuid4().hex[:10], "job": job["id"], "export": e["n"], "clip_i": e.get("i"), "platform": platform,
             "title": e.get("title", ""), "caption": str(sp.get("caption", ""))[:2200],
             "hashtags": [str(h)[:40] for h in (sp.get("hashtags") or [])][:20], "when": when or None,
             "privacy": sp.get("privacy") or "SELF_ONLY", "tt_mode": "draft" if sp.get("tt_mode") == "draft" else "direct",
             "status": "pending", "stage": "", "error": None, "result": None, "created": now(), "tries": 0, "next_try": 0,
             "native": False, "progress": 0}
        # Facebook sabe programar solo: 10 min a 30 dias en el futuro -> se sube ya y Facebook lo publica
        if platform == "facebook" and when and 11 * 60 <= when - now() <= 29 * 86400:
            t["native"] = True
        with Q_LOCK:
            QUEUE.append(t)
        made.append(t)
    save_queue()
    return made, errs


def due(t):
    if t["status"] != "pending" or t.get("next_try", 0) > now():
        return False
    if t.get("native") or not t.get("when"):
        return True
    return t["when"] <= now()


def run_task(t):
    with TASK_SEM:
        if t["status"] != "pending":
            return
        t["status"], t["error"], t["stage"] = "running", None, "Preparando…"
        save_queue()
        try:
            job, e = task_file(t)
            if e["status"] in ("queued", "running"):
                t["status"], t["stage"], t["next_try"] = "pending", "Esperando a que termine el clip…", now() + 10
                return
            if e["status"] != "done" or not e.get("file"):
                raise PermanentError("El clip no se pudo crear: " + str(e.get("error") or e["status"]))
            path = job["dir"] / e["file"]
            if not path.exists():
                raise PermanentError("No encuentro el archivo del clip.")
            res = post_facebook(t, path) if t["platform"] == "facebook" else post_tiktok(t, path)
            t["status"], t["result"], t["stage"], t["done_at"] = "done", res, "Listo", now()
        except PermanentError as ex:
            t["status"], t["error"] = "error", str(ex)
        except Exception as ex:
            t["tries"] += 1
            if t["tries"] >= MAX_TRIES:
                t["status"], t["error"] = "error", f"{ex} (falló {t['tries']} veces)"
            else:
                t["status"], t["next_try"], t["stage"] = "pending", now() + RETRY_WAIT, f"Reintento {t['tries']}/{MAX_TRIES}"
                t["error"] = str(ex)[:250]
        finally:
            save_queue()


def scheduler_loop():
    while True:
        try:
            for t in list(QUEUE):
                if due(t) and not t.get("_started"):
                    t["_started"] = True

                    def go(tt=t):
                        try:
                            run_task(tt)
                        finally:
                            tt["_started"] = False
                    threading.Thread(target=go, daemon=True).start()
        except Exception:
            pass
        time.sleep(float(os.environ.get("CH_TICK", 15)))


def cancel_task(tid):
    t = next((x for x in QUEUE if x["id"] == tid), None)
    if t and t["status"] == "pending":
        t["status"], t["error"] = "cancelled", None
        save_queue()
        return True
    return False


def queue_view():
    out = []
    for t in sorted(QUEUE, key=lambda x: (x.get("when") or x["created"])):
        d = {k: v for k, v in t.items() if not k.startswith("_")}
        d["when_txt"] = fmt_when(t["when"]) if t.get("when") else "Ahora"
        out.append(d)
    return out


# ---------------------------------------------------------------- textos sugeridos
CAT_TAGS = {"risas": ["risas", "funny", "gracioso"], "terror": ["susto", "terror", "miedo"],
            "polemica": ["polemica", "drama", "viral"], "epico": ["epico", "clutch", "gg"], "fail": ["fail", "epicfail", "lol"],
            "otro": ["clips", "gaming"], "susto": ["susto", "terror"], "hype": ["hype", "epico"], "fuerte": ["clips", "gaming"]}


def suggest_captions(job, ids):
    base = {}
    for i in ids:
        c = clip_by_i(job, i)
        if not c:
            continue
        cat = c.get("cat") or "otro"
        base[i] = {"i": i, "caption": c.get("title", ""), "hashtags": CAT_TAGS.get(cat, CAT_TAGS["otro"]) + ["kick", "streamer", "fyp"]}
    if get_key("anthropic_key") and base:
        try:
            items = [{"i": i, "title": clip_by_i(job, i).get("title", ""), "category": clip_by_i(job, i).get("cat", ""),
                      "transcript": (clip_by_i(job, i).get("transcript") or "")[:400]} for i in base]
            out = extract_json(call_claude(CAPTION_PROMPT, json.dumps(items, ensure_ascii=False), 1500), "[")
            for o in out:
                if o.get("i") in base:
                    base[o["i"]]["caption"] = str(o.get("caption", base[o["i"]]["caption"]))[:150]
                    tags = [str(x).lstrip("#") for x in o.get("hashtags", [])][:6]
                    if tags:
                        base[o["i"]]["hashtags"] = tags + ["fyp"] if "fyp" not in tags else tags
        except Exception:
            pass
    return list(base.values())


# ---------------------------------------------------------------- servidor web
app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = None  # sin límite: los directos de varias horas pesan mucho
JID_RE = re.compile(r"[0-9a-f]{12}")


def get_job(jid):
    if not JID_RE.fullmatch(jid) or jid not in JOBS:
        abort(404)
    return JOBS[jid]


def err(msg, code=400):
    return jsonify({"error": msg}), code


@app.get("/ping")
def ping():
    return "ok", 200


@app.get("/")
def index():
    return Response(INDEX_HTML, mimetype="text/html")


@app.get("/favicon.ico")
def favicon():
    return Response(status=204)


@app.get("/api/config")
def api_config_get():
    import importlib.util
    cfg = load_config()
    return jsonify({"ai": bool(get_key("anthropic_key")), "stt": bool(get_key("openai_key")),
                    "ai_mask": mask(get_key("anthropic_key")), "stt_mask": mask(get_key("openai_key")),
                    "ffmpeg": bool(shutil.which("ffmpeg")), "ytdlp": bool(ytdlp_cmd()), "font": bool(find_font()),
                    "impers": importlib.util.find_spec("curl_cffi") is not None,
                    "defaults": sanitize_settings(cfg.get("defaults") or {}), "port": PORT})


@app.post("/api/config")
def api_config_set():
    d = request.get_json(silent=True) or {}

    def fn(cfg):
        for k in ("anthropic_key", "openai_key"):
            if k in d:
                v = str(d.get(k, "")).strip()
                if v == "-":
                    cfg.pop(k, None)
                elif v:
                    cfg[k] = v
        if isinstance(d.get("defaults"), dict):
            cfg["defaults"] = sanitize_settings(d["defaults"])
    cfg_update(fn)
    return api_config_get()


# ---- trabajos
def export_eta(e):
    """Segundos que faltan para este clip (None si no se puede estimar todavia)."""
    try:
        pr = e.get("progress", 0)
        if e.get("status") == "running" and e.get("t_start") and pr >= 8:
            return int((now() - e["t_start"]) / pr * (100 - pr))
    except Exception:
        pass
    return None


def public_export(j, e):
    return {"n": e["n"], "i": e.get("i"), "status": e["status"], "progress": e.get("progress", 0), "stage": e.get("stage", ""),
            "error": e.get("error"), "title": e.get("title", ""), "layout": e.get("layout", ""), "ready": bool(e.get("file")),
            "dur": e.get("dur", 0), "log": e.get("log", [])[-3:], "created": e.get("created", 0), "eta": export_eta(e)}


def public_job(j):
    return {"id": j["id"], "label": j.get("label", ""), "created": j["created"], "status": j["status"],
            "progress": j["progress"], "stage": j["stage"], "log": j["log"][-25:], "error": j["error"],
            "base_offset": j["base_offset"], "ai": j["ai_used"], "facecam": j["facecam"], "facecam_src": j.get("facecam_src", ""),
            "auto": j.get("auto", False), "auto_pending": j.get("auto_pending", False),
            "settings": sanitize_settings(j.get("settings") or {}),
            "meta": j["meta"] and {"width": j["meta"]["width"], "height": j["meta"]["height"], "duration": j["meta"]["duration"]},
            "has_url": bool(j["params"].get("url")),
            "clips": [{k: c.get(k) for k in ("i", "start", "end", "t_peak", "intensity", "cat", "title", "reason", "layout", "cx", "cy",
                                             "zoom", "title_on", "transcript", "why", "voice", "words", "overlays", "cap_lines")}
                      | {"thumb": f"/api/file/{j['id']}/{c['thumb']}" if c.get("thumb") else ""} for c in j["clips"]],
            "exports": [public_export(j, e) for e in j["exports"]]}


@app.get("/api/jobs")
def api_jobs():
    out = [{"id": j["id"], "label": j.get("label", ""), "created": j["created"], "status": j["status"],
            "progress": j["progress"], "clips": len(j["clips"]),
            "done": sum(1 for e in j["exports"] if e["status"] == "done"), "exports": len(j["exports"])}
           for j in JOBS.values()]
    out.sort(key=lambda x: -x["created"])
    return jsonify(out)


@app.post("/api/analyze")
def api_analyze():
    if not shutil.which("ffmpeg"):
        return err("FFmpeg no está instalado (pkg install ffmpeg)", 500)
    url = request.form.get("url", "").strip()
    f = request.files.get("file")
    lpath = request.form.get("path", "").strip().strip('"').strip("'")
    if lpath:
        lp = Path(os.path.expanduser(lpath))
        if not lp.is_file():
            return err(f"No encuentro ese archivo en el celular: {lpath}. En Termux las descargas están en /sdcard/Download/ "
                       "(corre antes termux-setup-storage).")
    if not url and not lpath and not (f and f.filename):
        return err("Pega el link del VOD, escribe la ruta del archivo o sube un video")
    if url and not re.match(r"https?://", url):
        return err("El link debe empezar con http:// o https://")
    try:
        s_in = json.loads(request.form.get("settings") or "{}")
    except ValueError:
        s_in = {}
    settings = sanitize_settings(s_in, load_config().get("defaults"))
    params = {"url": url, "file_name": None, "t_from": parse_time(request.form.get("t_from")),
              "t_to": parse_time(request.form.get("t_to")),
              "n_clips": int(clamp(request.form.get("n_clips"), 1, 30, 8)),
              "clip_len": int(clamp(request.form.get("clip_len"), 10, 120, 40))}
    cleanup_old_jobs()
    label = (url.rstrip("/").split("/")[-1][:40] if url else (Path(lpath).name if lpath else (f.filename or "video"))[:40])
    job = new_job(params, label, settings, settings["auto_create"])
    file_name = None
    if lpath and not url:
        ext = lp.suffix.lower()
        file_name = "source" + (ext if re.fullmatch(r"\.[a-z0-9]{2,5}", ext) else ".mp4")
        try:
            os.symlink(lp.resolve(), job["dir"] / file_name)  # sin copiar: sirve para videos de muchas horas
        except OSError:
            shutil.copyfile(lp, job["dir"] / file_name)
        params["file_name"] = file_name
        job["orig"] = file_name
    elif f and f.filename and not url:
        ext = Path(f.filename).suffix.lower()
        file_name = "source" + (ext if re.fullmatch(r"\.[a-z0-9]{2,5}", ext) else ".mp4")
        f.save(job["dir"] / file_name)
        params["file_name"] = file_name
        job["orig"] = file_name

    def run():
        if file_name:
            try:
                job["orig_info"] = probe(job["dir"] / file_name)
            except Exception as e:
                job["status"], job["error"] = "error", str(e)
                save_job(job)
                return
        analyze_job(job)

    threading.Thread(target=run, daemon=True).start()
    return jsonify({"id": job["id"]})


@app.get("/api/job/<jid>")
def api_job(jid):
    return jsonify(public_job(get_job(jid)))


@app.delete("/api/job/<jid>")
def api_job_delete(jid):
    j = get_job(jid)
    if any(t["job"] == jid and t["status"] in PENDING for t in QUEUE):
        return err("Este trabajo tiene publicaciones pendientes. Cancélalas primero en la pestaña Cola.", 409)
    stop_job(j)
    delete_job(jid)
    return jsonify({"ok": True})


def stop_job(j):
    j["cancel"] = True
    for e in j["exports"]:
        e["cancel"] = True
        if e.get("proc"):
            try:
                e["proc"].terminate()
            except Exception:
                pass
    if j.get("proc"):
        try:
            j["proc"].terminate()
        except Exception:
            pass


@app.post("/api/cancel/<jid>")
def api_cancel(jid):
    j = get_job(jid)
    stop_job(j)
    return jsonify({"ok": True})


@app.get("/api/file/<jid>/<name>")
def api_file(jid, name):
    j = get_job(jid)
    if not re.fullmatch(r"(thumb_\d+|facecam_frame)\.jpg", name):
        abort(404)
    p = j["dir"] / name
    if not p.exists():
        abort(404)
    return send_file(p, mimetype="image/jpeg", max_age=0)


@app.get("/vod/<jid>")
def vod(jid):
    j = get_job(jid)
    if not j["low"]:
        abort(404)
    return send_file(j["dir"] / j["low"], conditional=True)


def maybe_auto_export(j):
    if j.get("auto_pending") and j["status"] == "ready":
        j["auto_pending"] = False
        start_export(j, [{"i": c["i"], "start": c["start"], "end": c["end"], "title": c["title"], "layout": ""}
                         for c in j["clips"]], j["settings"])


@app.post("/api/facecam/<jid>")
def api_facecam_set(jid):
    j = get_job(jid)
    d = request.get_json(silent=True) or {}
    x, y, w, h = (clamp(d.get(k), 0, 1, None) for k in ("x", "y", "w", "h"))
    if None in (x, y, w, h) or w < 0.04 or h < 0.04:
        return err("Rectángulo inválido")
    j["facecam"] = {"x": x, "y": y, "w": min(w, 1 - x), "h": min(h, 1 - y)}
    j["facecam_src"] = "manual"
    maybe_auto_export(j)
    save_job(j)
    return jsonify({"facecam": j["facecam"], "auto_started": not j.get("auto_pending")})


@app.post("/api/facecam/<jid>/detect")
def api_facecam_detect(jid):
    j = get_job(jid)
    if not get_key("anthropic_key"):
        return err("Para detectar la cámara con IA conecta tu clave de Anthropic. También puedes marcarla con el dedo.")
    try:
        fc = detect_facecam_ai(j)
    except Exception as e:
        msg = str(e)
        if "401" in msg or "authentication" in msg.lower():
            msg = ("Tu clave de Anthropic no es válida (error 401). Pega una clave que empiece con sk-ant- en Ajustes. "
                   "Se saca en console.anthropic.com y necesita saldo; el plan gratis de Claude no incluye clave. "
                   "Mientras tanto marca tu cámara con el dedo.")
        return err(f"No pude detectar la cámara: {msg[:300]}", 500)
    if not fc:
        return err("No encontré una cámara en ese fotograma. Márcala con el dedo.", 404)
    j["facecam"], j["facecam_src"] = fc, "ia"
    save_job(j)
    return jsonify({"facecam": fc})


@app.post("/api/settings/<jid>")
def api_job_settings(jid):
    j = get_job(jid)
    j["settings"] = sanitize_settings((request.get_json(silent=True) or {}), j.get("settings"))
    save_job(j)
    return jsonify({"settings": j["settings"]})


@app.post("/api/export/<jid>")
def api_export(jid):
    j = get_job(jid)
    if j["status"] != "ready":
        return err("El análisis aún no termina")
    d = request.get_json(silent=True) or {}
    s = sanitize_settings(d.get("settings") or {}, j.get("settings"))
    j["settings"] = s
    total = j["meta"]["duration"]
    items = []
    for c in (d.get("clips") or [])[:20]:
        orig = clip_by_i(j, c.get("i"))
        if not orig:
            continue
        st = clamp(c.get("start"), 0, total, orig["start"])
        en = clamp(c.get("end"), 0, total, orig["end"])
        if en - st < 3:
            continue
        en = min(en, st + 180)
        title = str(c.get("title", orig.get("title", "")))[:70]
        lay = c.get("layout") if c.get("layout") in LAYOUTS else ""
        extra = {"cx": clamp(c.get("cx"), 0, 1, 0.5), "cy": clamp(c.get("cy"), 0, 1, 0.5),
                 "zoom": clamp(c.get("zoom"), 1, 4, 1.0),
                 "title_on": (bool(c["title_on"]) if c.get("title_on") is not None else None),
                 "overlays": sanitize_overlays(c.get("overlays")), "bg": sanitize_bg(c.get("bg")),
                 "cap_lines": [[round(float(x[0]), 2), round(float(x[1]), 2), str(x[2])[:90]] for x in (c.get("cap_lines") or [])[:80]
                               if isinstance(x, (list, tuple)) and len(x) >= 3]}
        orig.update({"start": st, "end": en, "title": title, "layout": lay, **extra})
        items.append({"i": orig["i"], "start": st, "end": en, "title": title, "layout": lay, **extra})
    if not items:
        return err("No hay clips válidos para exportar")
    ns = start_export(j, items, s)
    save_job(j)
    return jsonify({"started": ns})


def find_export(jid, n):
    j = get_job(jid)
    e = next((x for x in j["exports"] if x["n"] == n), None)
    if not e:
        abort(404)
    return j, e


@app.post("/api/export/<jid>/<int:n>/cancel")
def api_export_cancel(jid, n):
    j, e = find_export(jid, n)
    e["cancel"] = True
    if e.get("proc"):
        try:
            e["proc"].terminate()
        except Exception:
            pass
    return jsonify({"ok": True})


@app.delete("/api/export/<jid>/<int:n>")
def api_export_delete(jid, n):
    j, e = find_export(jid, n)
    if any(t["job"] == jid and t["export"] == n and t["status"] in PENDING for t in QUEUE):
        return err("Este clip tiene una publicación pendiente. Cancélala primero.", 409)
    if e["status"] in ("queued", "running"):
        return err("Cancela el clip antes de borrarlo.", 409)
    if e.get("file"):
        try:
            (j["dir"] / e["file"]).unlink()
        except Exception:
            pass
    j["exports"].remove(e)
    save_job(j)
    return jsonify({"ok": True})


@app.get("/clipfile/<jid>/<int:n>")
def clipfile(jid, n):
    j, e = find_export(jid, n)
    if not e.get("file"):
        abort(404)
    name = re.sub(r"[^A-Za-z0-9_-]+", "_", e.get("title") or f"clip{n}")[:40] or f"clip{n}"
    return send_file(j["dir"] / e["file"], mimetype="video/mp4", conditional=True,
                     as_attachment=request.args.get("dl") == "1", download_name=f"{name}.mp4")


@app.get("/api/frame/<jid>/<int:t>")
def api_frame(jid, t):
    """Un cuadro del video en el segundo t (para elegir el recorte de cada clip)."""
    j = get_job(jid)
    if not j.get("low"):
        abort(404)
    t = int(clamp(t, 0, max(0, int(j["meta"]["duration"]) - 1), 0))
    name = f"frame_{t}.jpg"
    p = j["dir"] / name
    if not p.exists():
        r = subprocess.run(["ffmpeg", "-y", "-v", "error", "-nostdin", "-ss", str(t), "-i", str(j["dir"] / j["low"]),
                            "-frames:v", "1", "-vf", "scale='min(720,iw)':-2", "-q:v", "4", name],
                           cwd=j["dir"], capture_output=True)
        if r.returncode or not p.exists():
            abort(404)
        old = sorted(j["dir"].glob("frame_*.jpg"), key=lambda x: x.stat().st_mtime)[:-40]
        for o in old:
            o.unlink(missing_ok=True)
    return send_file(p, mimetype="image/jpeg", max_age=3600)


# ---------------------------------------------------------------- subtitulos editables, plantillas, referencia, agente
TEMPLATES_FILE = DATA / "templates.json"
TPL_LOCK = threading.Lock()


def load_templates():
    try:
        return json.loads(TEMPLATES_FILE.read_text(encoding="utf-8"))
    except Exception:
        return []


def save_templates(lst):
    with TPL_LOCK:
        TEMPLATES_FILE.write_text(json.dumps(lst, ensure_ascii=False), encoding="utf-8")


@app.post("/api/captions/<jid>")
def api_captions(jid):
    """Transcribe un tramo del clip y devuelve las lineas de subtitulos para corregirlas antes de renderizar."""
    j = get_job(jid)
    if j["status"] != "ready" or not j.get("low"):
        return err("El análisis aún no termina")
    if not get_key("openai_key"):
        return err("Para sacar los subtítulos hace falta la clave de OpenAI (Ajustes → Mi cuenta).")
    d = request.get_json(silent=True) or {}
    total = j["meta"]["duration"]
    st = clamp(d.get("start"), 0, total, 0)
    en = clamp(d.get("end"), 0, total, min(total, st + 30))
    if en - st < 2:
        return err("El clip es muy corto")
    try:
        cut_audio(j, str(j["dir"] / j["low"]), st, min(en - st, 180), "capedit.mp3")
        data = whisper(j["dir"] / "capedit.mp3", verbose=True)
    except Exception as e:
        msg = str(e)
        return err("No pude escuchar el clip: " + ("tu clave de OpenAI no es válida." if "401" in msg else msg[:200]), 500)
    lines = [[round(a, 2), round(b, 2), t] for a, b, t in caption_items(data, en - st)]
    return jsonify({"lines": lines})


@app.get("/api/templates")
def api_templates():
    return jsonify(load_templates())


@app.post("/api/templates")
def api_templates_add():
    d = request.get_json(silent=True) or {}
    name = str(d.get("name", "")).strip()[:40]
    if not name:
        return err("Ponle un nombre a la plantilla")
    st = sanitize_settings(d.get("settings") or {})
    st.pop("auto_create", None)
    lst = [t for t in load_templates() if t["name"].lower() != name.lower()]
    lst.append({"id": uuid.uuid4().hex[:8], "name": name, "settings": st, "created": now()})
    save_templates(lst[-30:])
    return jsonify(lst[-30:])


@app.delete("/api/templates/<tid>")
def api_templates_del(tid):
    lst = [t for t in load_templates() if t["id"] != tid]
    save_templates(lst)
    return jsonify(lst)


REFERENCE_PROMPT = """You help a streamer recreate the editing style of a REFERENCE short vertical video (TikTok/Reels clip) for his own clips.
You get some frames of the reference (maybe none) and the streamer's instructions. Work out how it was edited and return ONLY JSON:
{"layout": "fill"|"split"|"circle"|"dual", "titles": true|false, "captions": true|false, "caption_style": "karaoke"|"simple",
 "zoom_peak": true|false, "logo_pos": "tl"|"tr"|"bl"|"br"|"",
 "overlays": [{"type": "text", "text": <a FIXED label that stays on screen, e.g. channel name / handle / watermark / "KICK  Name">,
   "x": <center 0-1>, "y": <center 0-1>, "size": <font size as fraction of video width, 0.03-0.12>, "color": "rrggbb",
   "bg": "none"|"outline"|"card"|"box", "t0": 0, "t1": -1}],
 "notes": <one short Spanish sentence describing the style>}
Rules: the per-clip headline card and the spoken subtitles are NOT overlays (use titles/captions). Only fixed labels or watermarks are overlays.
If the video shows another streamer's name, REPLACE it with the new name the streamer gives you. Never copy someone else's name.
If the streamer wrote instructions, follow them (they win over what you see). Use at most 6 overlays. Text in Spanish unless the video says otherwise."""


def _reference_friendly(msg):
    if "401" in msg or "authentication" in msg.lower():
        return ("Tu clave de Anthropic no es válida (error 401). Pega una que empiece con sk-ant- en Ajustes → Mi cuenta. "
                "Se saca en console.anthropic.com y necesita saldo.")
    return msg[:300]


def _style_from_ai(o):
    st = {}
    if o.get("layout") in ("fill", "split", "circle", "dual"):
        st["layout"] = o["layout"]
    for k in ("titles", "captions", "zoom_peak"):
        if isinstance(o.get(k), bool):
            st[k] = o[k]
    if o.get("caption_style") in ("karaoke", "simple"):
        st["caption_style"] = o["caption_style"]
    if o.get("logo_pos") in ("tl", "tr", "bl", "br"):
        st["logo_pos"] = o["logo_pos"]
    ovs = sanitize_overlays([x for x in (o.get("overlays") or []) if isinstance(x, dict) and x.get("type") == "text"])
    return {"settings": st, "overlays": ovs, "notes": str(o.get("notes", ""))[:200]}


def _ai_style(frames, new_name, prompt):
    content = []
    for f in frames:
        content.append(img_block(f))
    txt = f"Nuevo nombre del streamer: {new_name or '(no dado)'}\nInstrucciones del streamer: {prompt or '(ninguna)'}\n"
    txt += "Devuelve el JSON ahora." if frames else "No hay video de referencia: usa solo las instrucciones. Devuelve el JSON ahora."
    content.append({"type": "text", "text": txt})
    raw = call_claude(REFERENCE_PROMPT, content, max_tokens=1500)
    return _style_from_ai(extract_json(raw, "{"))


@app.post("/api/reference")
def api_reference():
    """Edicion con video de referencia: lee su estilo (textos fijos, marca, diseno) y lo adapta al nombre del streamer."""
    if not get_key("anthropic_key"):
        return err("Para leer el video de referencia hace falta una clave de Anthropic válida (Ajustes → Mi cuenta).")
    name = request.form.get("name", "").strip()[:40]
    prompt = request.form.get("prompt", "").strip()[:600]
    f = request.files.get("file")
    tmp = DATA / f"ref_{uuid.uuid4().hex[:8]}"
    tmp.mkdir(parents=True, exist_ok=True)
    try:
        frames = []
        if f and f.filename:
            vp = tmp / ("ref" + (Path(f.filename).suffix.lower() or ".mp4"))
            f.save(vp)
            try:
                dur = probe(vp)["duration"]
            except Exception:
                return err("No pude abrir ese video de referencia.")
            for k, frac in enumerate((0.08, 0.3, 0.55, 0.8)):
                nm = tmp / f"f{k}.jpg"
                subprocess.run(["ffmpeg", "-y", "-v", "error", "-nostdin", "-ss", f"{dur * frac:.2f}", "-i", str(vp),
                                "-frames:v", "1", "-vf", "scale='min(540,iw)':-2", "-q:v", "5", str(nm)], capture_output=True)
                if nm.exists():
                    frames.append(nm)
        if not frames and not prompt:
            return err("Sube un video de referencia o escribe lo que quieres.")
        try:
            res = _ai_style(frames, name, prompt)
        except Exception as e:
            return err("No pude analizar la referencia: " + _reference_friendly(str(e)), 500)
        return jsonify(res)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


@app.post("/api/agent")
def api_agent():
    """Agente IA: escribes lo que quieres ('subtítulos amarillos, mi nombre arriba…') y devuelve ajustes + textos."""
    if not get_key("anthropic_key"):
        return err("El Agente IA necesita una clave de Anthropic válida (Ajustes → Mi cuenta).")
    d = request.get_json(silent=True) or {}
    prompt = str(d.get("prompt", "")).strip()[:800]
    if not prompt:
        return err("Escribe qué quieres que haga")
    try:
        return jsonify(_ai_style([], str(d.get("name", ""))[:40], prompt))
    except Exception as e:
        return err("No pude: " + _reference_friendly(str(e)), 500)


@app.get("/manifest.json")
def manifest():
    return jsonify({"name": "Lico Clips", "short_name": "Lico Clips", "start_url": "/", "display": "standalone",
                    "background_color": "#071a2b", "theme_color": "#38bdf8",
                    "icons": [{"src": "/icon.svg", "sizes": "any", "type": "image/svg+xml", "purpose": "any"}]})


@app.get("/icon.svg")
def icon_svg():
    svg = ('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 100 100"><rect width="100" height="100" rx="24" fill="#38bdf8"/>'
           '<path d="M38 28v44l36-22z" fill="#06223a"/></svg>')
    return Response(svg, mimetype="image/svg+xml")


@app.get("/sw.js")
def sw_js():
    return Response("self.addEventListener('fetch',()=>{});", mimetype="application/javascript")


@app.get("/api/home")
def api_home():
    exports_done = sum(1 for j in JOBS.values() for e in j["exports"] if e["status"] == "done")
    published = sum(1 for t in QUEUE if t["status"] == "done")
    waiting = sum(1 for t in QUEUE if t["status"] in PENDING)
    top = []
    for j in JOBS.values():
        for c in j["clips"]:
            ex = [e for e in j["exports"] if e.get("i") == c["i"] and e["status"] == "done"]
            top.append({"job": j["id"], "i": c["i"], "title": c.get("title", ""), "cat": c.get("cat", ""),
                        "score": int(round((c.get("intensity") or 0) * 10)), "dur": int(c["end"] - c["start"]),
                        "thumb": f"/api/file/{j['id']}/{c['thumb']}" if c.get("thumb") else "",
                        "clip": f"/clipfile/{j['id']}/{max(e['n'] for e in ex)}" if ex else ""})
    top.sort(key=lambda x: -x["score"])
    cats = {}
    for t_ in top:
        cats[t_["cat"] or "otro"] = cats.get(t_["cat"] or "otro", 0) + 1
    avg = round(sum(t_["score"] for t_ in top) / len(top), 1) if top else 0
    return jsonify({"jobs": len(JOBS), "clips": exports_done, "published": published, "waiting": waiting, "top": top[:12],
                    "cats": cats, "avg": avg, "found": len(top),
                    "fb": sum(1 for t in QUEUE if t["status"] == "done" and t.get("platform") == "facebook"),
                    "tt": sum(1 for t in QUEUE if t["status"] == "done" and t.get("platform") == "tiktok")})


# ---- recursos (musica, logo)
@app.get("/assets/<name>")
def asset_file(name):
    if not ASSET_RE.match(name):
        abort(404)
    p = ASSETS_DIR / name
    if not p.is_file():
        abort(404)
    return send_file(p)


@app.get("/api/assets")
def api_assets():
    out = []
    for p in sorted(ASSETS_DIR.iterdir()):
        if p.is_file() and not p.name.startswith("sfx_"):
            kind = "music" if p.suffix.lower() in (".mp3", ".m4a", ".aac", ".wav", ".ogg") else "logo"
            out.append({"name": p.name, "kind": kind, "size": p.stat().st_size})
    return jsonify(out)


@app.post("/api/assets")
def api_assets_add():
    f = request.files.get("file")
    if not f or not f.filename:
        return err("Elige un archivo")
    ext = Path(f.filename).suffix.lower()
    if ext not in (".mp3", ".m4a", ".aac", ".wav", ".ogg", ".png", ".jpg", ".jpeg", ".webp"):
        return err("Usa música (mp3, m4a, wav, ogg) o una imagen (png, jpg, webp)")
    stem = re.sub(r"[^A-Za-z0-9_-]+", "_", (request.form.get("label") or "").strip() or Path(f.filename).stem).strip("_")[:50] or "recurso"
    name = stem + ext
    k = 1
    while (ASSETS_DIR / name).exists():
        k += 1
        name = f"{stem}_{k}{ext}"
    f.save(ASSETS_DIR / name)
    return jsonify({"name": name})


@app.delete("/api/assets/<name>")
def api_assets_del(name):
    p = asset_path(name)
    if not p:
        abort(404)
    p.unlink()
    return jsonify({"ok": True})


# ---- cuentas
@app.get("/api/accounts")
def api_accounts():
    return jsonify(accounts_view())


@app.post("/api/fb/app")
def api_fb_app():
    d = request.get_json(silent=True) or {}
    a = account("facebook")
    if str(d.get("app_id", "")).strip():
        a["app_id"] = str(d["app_id"]).strip()
    if str(d.get("app_secret", "")).strip():
        a["app_secret"] = str(d["app_secret"]).strip()
    set_account("facebook", a)
    return jsonify(accounts_view())


@app.get("/api/fb/login")
def api_fb_login():
    try:
        return redirect(fb_login_url())
    except Exception as e:
        return Response(f"<meta charset=utf-8><p>{e}</p><p><a href='/'>Volver</a></p>", status=400, mimetype="text/html")


@app.get("/api/fb/callback")
def api_fb_callback():
    if request.args.get("error"):
        msg = request.args.get("error_description") or request.args.get("error")
        return Response(f"<meta charset=utf-8><p>Facebook: {msg}</p><p><a href='/'>Volver</a></p>", status=400, mimetype="text/html")
    try:
        fb_finish_login(request.args.get("code", ""), request.args.get("state", ""))
    except Exception as e:
        return Response(f"<meta charset=utf-8><p>{e}</p><p><a href='/'>Volver</a></p>", status=400, mimetype="text/html")
    return redirect("/#cuentas")


@app.post("/api/fb/page")
def api_fb_page():
    try:
        fb_select_page((request.get_json(silent=True) or {}).get("id", ""))
    except Exception as e:
        return err(str(e))
    return jsonify(accounts_view())


@app.post("/api/fb/manual")
def api_fb_manual():
    d = request.get_json(silent=True) or {}
    try:
        fb_manual(d.get("page_id"), d.get("token"))
    except Exception as e:
        return err(str(e))
    return jsonify(accounts_view())


@app.post("/api/fb/disconnect")
def api_fb_disc():
    a = account("facebook")
    for k in ("page_id", "page_name", "page_token", "pages", "state"):
        a.pop(k, None)
    set_account("facebook", a)
    return jsonify(accounts_view())


@app.post("/api/tt/app")
def api_tt_app():
    d = request.get_json(silent=True) or {}
    a = account("tiktok")
    for k in ("client_key", "client_secret", "redirect_uri"):
        if str(d.get(k, "")).strip():
            a[k] = str(d[k]).strip()
    if a.get("redirect_uri") and not a["redirect_uri"].startswith("https://"):
        return err("TikTok exige que la Redirect URI empiece con https://")
    set_account("tiktok", a)
    return jsonify(accounts_view())


@app.get("/api/tt/login")
def api_tt_login():
    try:
        return jsonify({"url": tt_login_url()})
    except Exception as e:
        return err(str(e))


@app.post("/api/tt/finish")
def api_tt_finish():
    try:
        tt_finish_login((request.get_json(silent=True) or {}).get("pasted"))
    except Exception as e:
        return err(str(e))
    return jsonify(accounts_view())


@app.get("/api/tt/creator")
def api_tt_creator():
    try:
        info = tt_creator_info()
    except Exception as e:
        return err(str(e))
    return jsonify({"privacy": info.get("privacy_level_options") or ["SELF_ONLY"],
                    "max_sec": info.get("max_video_post_duration_sec"), "name": info.get("creator_nickname", "")})


@app.post("/api/tt/disconnect")
def api_tt_disc():
    a = account("tiktok")
    for k in ("access_token", "refresh_token", "open_id", "expires_at", "display_name", "state"):
        a.pop(k, None)
    set_account("tiktok", a)
    return jsonify(accounts_view())


# ---- publicar / cola
@app.post("/api/title/<jid>/<int:n>")
def api_title(jid, n):
    j = get_job(jid)
    c = clip_by_i(j, n)
    if not c:
        return err("Clip no encontrado", 404)
    if not get_key("anthropic_key"):
        return err("Falta la clave de Anthropic en Ajustes para usar la IA")
    try:
        txt = call_claude("Eres editor de clips virales de streams para TikTok/Reels. Lee lo que se dice en el clip y escribe UN título corto "
                          "(máx 60 caracteres), en español, que dé curiosidad y describa lo que pasa. Sin groserías, sin comillas, sin hashtags. "
                          "Responde solo el título.",
                          json.dumps({"categoria": c.get("cat", ""), "titulo_actual": c.get("title", ""),
                                      "transcripcion": (c.get("transcript") or "")[:600]}, ensure_ascii=False), 120)
        return jsonify({"title": txt.strip().strip('"')[:70]})
    except Exception as e:
        return err(f"La IA no pudo: {e}", 500)


@app.post("/api/suggest/<jid>")
def api_suggest(jid):
    j = get_job(jid)
    ids = [int(i) for i in ((request.get_json(silent=True) or {}).get("ids") or []) if str(i).isdigit()]
    return jsonify(suggest_captions(j, ids))


@app.post("/api/publish")
def api_publish():
    d = request.get_json(silent=True) or {}
    specs = (d.get("items") or [])[:60]
    made, errs = add_tasks(specs)
    return jsonify({"created": len(made), "errors": errs})


@app.get("/api/queue")
def api_queue():
    return jsonify(queue_view())


@app.post("/api/queue/<tid>/cancel")
def api_queue_cancel(tid):
    return jsonify({"ok": cancel_task(tid)})


@app.post("/api/queue/<tid>/retry")
def api_queue_retry(tid):
    t = next((x for x in QUEUE if x["id"] == tid), None)
    if not t or t["status"] not in ("error", "cancelled"):
        return err("Esa publicación no se puede reintentar")
    if t.get("when") and t["when"] < now():
        t["when"] = None
        t["native"] = False
    t.update({"status": "pending", "error": None, "tries": 0, "next_try": 0, "stage": ""})
    save_queue()
    return jsonify({"ok": True})


@app.delete("/api/queue/<tid>")
def api_queue_delete(tid):
    t = next((x for x in QUEUE if x["id"] == tid), None)
    if not t or t["status"] in PENDING:
        return err("Cancela la publicación antes de borrarla")
    with Q_LOCK:
        QUEUE.remove(t)
    save_queue()
    return jsonify({"ok": True})


INDEX_HTML = r"""<!doctype html>
<html lang="es">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="theme-color" content="#06121f"><link rel="manifest" href="/manifest.json"><link rel="icon" href="/icon.svg">
<title>Lico Clips</title>
<style>
:root{--bg:#06121f;--bg2:#0a1c2e;--card:#0e2338;--card2:#143049;--line:#22496a;--tx:#eaf6ff;--mut:#8fb0c9;--ac:#38bdf8;--acx:#06223a;--ac2:#34d399;--warn:#fbbf24;--bad:#fb7185;--r:14px}
:root[data-theme="light"]{--bg:#e8f5ff;--bg2:#ffffff;--card:#ffffff;--card2:#e0f1fd;--line:#b6d9f0;--tx:#06223a;--mut:#47698a;--ac:#0ea5e9;--acx:#ffffff;--ac2:#059669;--warn:#b45309;--bad:#e11d48}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
html,body{margin:0;background:var(--bg);color:var(--tx);font:15px/1.4 system-ui,-apple-system,Segoe UI,Roboto,sans-serif}
body{background:radial-gradient(1200px 600px at 80% -10%,#0c3b5c55,transparent),var(--bg)}
h1{font-size:20px;margin:16px 0 4px} h2{font-size:17px;margin:0 0 10px} h3{font-size:15px;margin:14px 0 6px}
.sub{color:var(--mut);font-size:13px}
.card{background:var(--card);border:1px solid var(--line);border-radius:var(--r);padding:14px;margin-bottom:12px}
label{display:block;font-size:13px;color:var(--mut);margin:10px 0 4px}
input[type=text],input[type=url],input[type=number],input[type=password],input[type=datetime-local],select,textarea{width:100%;background:var(--card2);color:var(--tx);border:1px solid var(--line);border-radius:10px;padding:11px;font:inherit}
textarea{min-height:64px;resize:vertical}
input[type=range]{width:100%;accent-color:var(--ac)}.sub b,.tiny b{color:var(--tx)}
input[type=file]{width:100%;color:var(--mut)}
button{font:inherit;cursor:pointer}
.btn{background:var(--ac);color:var(--acx);border:0;border-radius:11px;padding:12px 16px;font-weight:700}
.btn.sec{background:var(--card2);color:var(--tx);border:1px solid var(--line)}
.btn.ok{background:var(--ac2);color:#06231b}.btn.lg{padding:15px 18px;font-size:16px;border-radius:13px}
.btn.bad{background:transparent;color:var(--bad);border:1px solid var(--bad)}
.btn.sm{padding:7px 11px;font-size:13px;border-radius:9px}
.btn:disabled{opacity:.5}
.row{display:flex;gap:8px;align-items:center;flex-wrap:wrap}
.row>.grow{flex:1;min-width:0}
.g2{display:grid;grid-template-columns:1fr 1fr;gap:10px}
.chk{display:flex;gap:9px;align-items:center;margin:9px 0;color:var(--tx);font-size:14px}
.chk input{width:20px;height:20px;accent-color:var(--ac)}
.bar{height:9px;background:var(--card2);border-radius:9px;overflow:hidden;margin:8px 0}
.bar>i{display:block;height:100%;background:var(--ac);width:0;transition:width .4s}
.pill{display:inline-block;font-size:11px;font-weight:700;padding:2px 8px;border-radius:99px;background:var(--card2);color:var(--mut)}
.pill.risas{background:#3a3412;color:#ffd84d}.pill.terror{background:#3a1220;color:#ff6b8a}.pill.polemica{background:#3a2412;color:#ff9a4d}
.pill.epico{background:#142a3a;color:#5cc8ff}.pill.fail{background:#2a1a3a;color:#c58cff}.pill.susto{background:#3a1220;color:#ff6b8a}.pill.hype{background:#142a3a;color:#5cc8ff}
.pill.ok{background:#0f3328;color:var(--ac2)}.pill.err{background:#3a1218;color:var(--bad)}.pill.warn{background:#3a2d0f;color:var(--warn)}
.msg{padding:10px 12px;border-radius:10px;margin:10px 0;font-size:13.5px}
.msg.bad{background:#2b1118;border:1px solid #5b2230;color:#ffb3bd}
.msg.warn{background:#2b2411;border:1px solid #5b4a1c;color:#ffd98a}
.msg.ok{background:#0f2b22;border:1px solid #1d5b46;color:#9df0d4}
.hide{display:none!important}
details{background:var(--card2);border-radius:11px;padding:2px 12px;margin:10px 0}
summary{padding:10px 0;font-weight:600;cursor:pointer}
.clip{display:grid;grid-template-columns:96px 1fr;gap:12px}
.clip .th{width:96px;aspect-ratio:9/12;border-radius:10px;background:#000 center/cover;position:relative}
.clip .th b{position:absolute;left:4px;bottom:4px;background:#000a;border-radius:6px;padding:1px 6px;font-size:11px}
.mini{display:grid;grid-template-columns:1fr 1fr;gap:6px}
video{width:100%;max-height:420px;background:#000;border-radius:10px}
.camwrap{position:relative;touch-action:none;user-select:none;margin:8px 0}
.camwrap img{width:100%;display:block;border-radius:10px}
.camrect{position:absolute;border:3px solid var(--ac);background:#38bdf822;border-radius:6px}
.camrect i{position:absolute;right:-12px;bottom:-12px;width:28px;height:28px;border-radius:50%;background:var(--ac);border:3px solid var(--acx)}
.prev{width:84px;aspect-ratio:9/16;background:#222;border-radius:8px;overflow:hidden;display:flex;flex-direction:column;flex:0 0 auto;border:1px solid var(--line);position:relative}
.prev div{display:flex;align-items:center;justify-content:center;font-size:10px;font-weight:700}
.prev .c{background:#3ddc97;color:#06231b}.prev .g{background:#38bdf8;color:#06223a}
.prev .dot{position:absolute;width:34%;aspect-ratio:1;border-radius:50%;background:#3ddc97;right:6%;bottom:12%;border:2px solid #fff}
.modal{position:fixed;inset:0;background:#000b;z-index:20;display:flex;align-items:flex-end;justify-content:center}
.modal>div{background:var(--bg);width:100%;max-width:900px;max-height:94vh;overflow:auto;border-radius:18px 18px 0 0;padding:16px;border:1px solid var(--line)}
.q{display:grid;grid-template-columns:1fr auto;gap:8px;align-items:center}
a{color:var(--ac2)}
.tiny{font-size:12px;color:var(--mut)}
code{background:var(--card2);padding:1px 6px;border-radius:6px;font-size:12.5px;word-break:break-all}
ol{padding-left:20px;margin:6px 0} li{margin:5px 0}
.stats{display:grid;grid-template-columns:repeat(4,1fr);gap:8px;margin:12px 0}
.stat{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:10px 6px;text-align:center}
.stat b{display:block;font-size:22px;color:var(--ac)}.stat span{font-size:11px;color:var(--mut)}
.hero{background:linear-gradient(135deg,#0c3b5c,#0e2338);border:1px solid #22496a;border-radius:16px;padding:16px;margin:12px 0}
.hero h2{font-size:19px}
.rail{display:flex;gap:12px;overflow-x:auto;padding-bottom:8px;scroll-snap-type:x mandatory}
.rail>.cc{flex:0 0 150px;scroll-snap-align:start}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(170px,1fr));gap:12px}
.cc{background:var(--card);border:1px solid var(--line);border-radius:14px;overflow:hidden;display:flex;flex-direction:column}
.cc .vid{position:relative;aspect-ratio:9/16;background:#000 center/cover no-repeat;overflow:hidden}
.cc .vid video{width:100%;height:100%;object-fit:cover;border-radius:0;max-height:none;position:absolute;inset:0}
.cc .rk{position:absolute;left:6px;top:6px;background:#000b;color:#fff;border-radius:7px;padding:1px 7px;font-weight:800;font-size:12px;z-index:2}
.cc .sc{position:absolute;right:6px;top:6px;width:36px;height:36px;border-radius:50%;background:#000c;border:3px solid var(--ac);color:#fff;font-weight:800;font-size:13px;display:flex;align-items:center;justify-content:center;z-index:2}
.cc .sc.hi{border-color:#3ddc97}.cc .sc.lo{border-color:#ff9a4d}
.cc .du{position:absolute;right:6px;bottom:6px;background:#000b;border-radius:6px;padding:1px 6px;font-size:11px;z-index:2}
.cc .cap{position:absolute;left:8px;right:8px;top:18%;background:#fff;color:#111;border-radius:8px;padding:5px 7px;font-weight:800;font-size:12px;text-align:center;z-index:1;pointer-events:none;line-height:1.2}
.cc .ov{position:absolute;inset:0;display:flex;flex-direction:column;align-items:center;justify-content:center;background:#000a;z-index:3;padding:10px;text-align:center;gap:6px}
.cc .ov .bar{width:80%}
.cc .bd{padding:8px;display:flex;flex-direction:column;gap:6px}
.cc .ttl{font-weight:700;font-size:13px;line-height:1.25;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
.cc .acts{display:flex;gap:6px;flex-wrap:wrap}
.cc .acts .btn{flex:1;padding:8px 6px;font-size:12.5px}
.big{display:grid;grid-template-columns:minmax(0,260px) 1fr;gap:14px}
.seg{display:flex;gap:6px;flex-wrap:wrap}
.seg button{background:var(--card2);border:1px solid var(--line);color:var(--tx);border-radius:10px;padding:8px 10px;font-size:12.5px;font-weight:600}
.seg button.on{background:var(--ac);color:var(--acx);border-color:var(--ac)}
.cropwrap{position:relative;touch-action:none;user-select:none;max-width:420px;margin:8px auto}
.cropwrap img{width:100%;display:block;border-radius:8px}
.crop9{position:absolute;top:0;border:3px solid var(--ac);box-shadow:0 0 0 999px #000a;border-radius:4px;cursor:grab}
.phone{width:100%;aspect-ratio:9/16;background:#000;border-radius:14px;overflow:hidden;position:relative}
.phone video{width:100%;height:100%;object-fit:cover;max-height:none;border-radius:0}
@media(min-width:720px){body{padding-top:8px}.modal{align-items:center}.modal>div{border-radius:18px}}
@media(max-width:640px){.big{grid-template-columns:1fr}.phone{max-width:240px;margin:0 auto}}

.app{display:flex;min-height:100vh;position:relative}
.side{width:240px;flex:0 0 240px;position:sticky;top:0;height:100vh;overflow:auto;background:color-mix(in srgb,var(--bg2) 94%,transparent);border-right:1px solid var(--line);padding:14px 12px;display:flex;flex-direction:column;gap:6px;z-index:30}
.brand{display:flex;align-items:center;gap:10px;padding:4px 6px 10px;font-weight:800;font-size:19px;letter-spacing:-.3px}
.brand .lg{width:38px;height:38px;border-radius:11px;background:var(--ac);color:var(--acx);display:flex;align-items:center;justify-content:center;font-size:20px}
.brand small{display:block;font-size:10.5px;font-weight:600;color:var(--mut);letter-spacing:0}
.side .newbtn{background:var(--ac);color:var(--acx);border:0;border-radius:11px;padding:11px;font-weight:800;margin:4px 0 8px}
.side h6{margin:12px 8px 4px;font-size:10.5px;letter-spacing:.9px;color:var(--mut);font-weight:700}
.side .it{display:flex;align-items:center;gap:11px;background:none;border:0;color:var(--mut);padding:10px 11px;border-radius:11px;font-weight:600;text-align:left;position:relative}
.side .it .ic{width:22px;text-align:center;font-size:17px}
.side .it:hover{background:var(--card2);color:var(--tx)}
.side .it.on{background:var(--card2);color:var(--ac)}
.side .badge{margin-left:auto;background:var(--ac);color:var(--acx);border-radius:9px;padding:0 7px;font-size:11px;font-weight:800}
.side .sys{margin-top:auto;background:var(--card);border:1px solid var(--line);border-radius:12px;padding:10px;font-size:12px;color:var(--mut)}
.side .sys b{color:var(--tx)} .dot{display:inline-block;width:8px;height:8px;border-radius:50%;background:var(--ac2);margin-right:6px}
.chipx{display:inline-block;background:var(--card2);border:1px solid var(--line);border-radius:8px;padding:2px 8px;margin:4px 4px 0 0;font-size:11.5px;color:var(--tx)}
.chipx.off{opacity:.55}
.main{flex:1;min-width:0;padding:16px 22px 80px;max-width:1180px;margin:0 auto}
.top{display:none}
.scrim{display:none}
#bgfx{position:fixed;inset:0;z-index:0;pointer-events:none;overflow:hidden}
#bgfx span{position:absolute;bottom:-60px;opacity:.13;animation:rise linear infinite;will-change:transform}
@keyframes rise{from{transform:translateY(0) rotate(0)}to{transform:translateY(-115vh) rotate(40deg)}}
@media (prefers-reduced-motion:reduce){#bgfx span{animation:none;bottom:auto}}
.tools{display:flex;gap:8px;flex-wrap:wrap;align-items:center;margin:10px 0}
.fchip{background:var(--card2);color:var(--mut);border:1px solid var(--line);border-radius:999px;padding:6px 12px;font-size:12.5px;font-weight:700}
.fchip.on{background:var(--ac);color:var(--acx);border-color:var(--ac)}
.cal{display:grid;grid-template-columns:repeat(7,1fr);gap:6px}
.cal .dn{font-size:11px;color:var(--mut);text-align:center;font-weight:700}
.cal .day{min-height:78px;background:var(--card);border:1px solid var(--line);border-radius:10px;padding:5px;font-size:12px;cursor:pointer;overflow:hidden}
.cal .day.out{opacity:.35} .cal .day.today{border-color:var(--ac)}
.cal .day b{color:var(--mut);font-size:11px}
.cal .ev{margin-top:3px;border-radius:6px;padding:1px 5px;font-size:10.5px;background:var(--card2);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.cal .ev.facebook{background:#1d4ed855}.cal .ev.tiktok{background:#db277755}
.stage{position:relative;aspect-ratio:9/16;background:#000 center/cover no-repeat;border-radius:14px;overflow:hidden;touch-action:none;user-select:none;width:100%}
.stage .ov{position:absolute;transform:translate(-50%,-50%);cursor:grab;white-space:nowrap;font-weight:800;line-height:1.1;padding:2px 6px;border:1px dashed #fff8}
.stage .ov.sel{border:2px solid var(--ac)}
.stage .ov img{display:block;width:100%}
.tabs{display:flex;gap:6px;flex-wrap:wrap;margin:6px 0 10px}
.tabs button{background:var(--card2);color:var(--mut);border:1px solid var(--line);border-radius:10px;padding:8px 12px;font-weight:700;font-size:13px}
.tabs button.on{background:var(--ac);color:var(--acx);border-color:var(--ac)}
.ovrow{display:flex;gap:6px;align-items:center;background:var(--card2);border-radius:10px;padding:6px 8px;margin:5px 0;cursor:pointer;border:1px solid transparent}
.ovrow.sel{border-color:var(--ac)}
.ovrow .nm{flex:1;min-width:0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;font-size:13px}
.big{display:grid;grid-template-columns:minmax(0,300px) 1fr;gap:16px}
:root[data-theme="light"] .msg.bad{background:#ffe4e9;border-color:#fda4b4;color:#9f1239}
:root[data-theme="light"] .msg.warn{background:#fef3c7;border-color:#fcd34d;color:#92400e}
:root[data-theme="light"] .msg.ok{background:#d1fae5;border-color:#6ee7b7;color:#065f46}
:root[data-theme="light"] .pill{background:#d6ecfb;color:#245}
@media(max-width:900px){
 .side{position:fixed;left:0;top:0;bottom:0;transform:translateX(-105%);transition:transform .22s;box-shadow:0 0 40px #000a;width:262px}
 body.menu .side{transform:none}
 body.menu .scrim{display:block;position:fixed;inset:0;background:#0009;z-index:25}
 .top{display:flex;align-items:center;gap:10px;position:sticky;top:0;z-index:20;background:color-mix(in srgb,var(--bg2) 94%,transparent);border-bottom:1px solid var(--line);padding:8px 12px}
 .top button{background:var(--card2);color:var(--tx);border:1px solid var(--line);border-radius:10px;padding:7px 11px;font-size:18px}
 .main{padding:12px 12px 80px}
}
@media(max-width:900px){
 .big{grid-template-columns:1fr!important;gap:8px}
 .big>div:first-child{position:sticky;top:0;z-index:6;background:var(--bg2);padding-bottom:4px}
 #e_stage{max-width:min(100%,calc(40vh*9/16));margin:0 auto}
 #e_tabs{position:fixed;left:0;right:0;bottom:0;z-index:60;margin:0;flex-wrap:nowrap;overflow-x:auto;gap:2px;padding:8px 8px calc(8px + env(safe-area-inset-bottom));background:var(--bg2);border-top:1px solid var(--line)}
 #e_tabs button{flex:0 0 auto;border:0;background:transparent;padding:8px 14px;font-size:12px;white-space:nowrap}
 #e_tabs button.on{background:var(--card2);color:var(--ac)}
 #e_pane{padding-bottom:70px}
}
@media(max-width:900px){
 .modal.editfs{align-items:stretch}
 .modal.editfs>div{max-height:none;height:100%;border-radius:0;border:0;background:#08090d;padding:10px 12px 90px}
 #e_tabs button{flex:1 1 0;display:flex;flex-direction:column;align-items:center;gap:2px;padding:6px 2px;font-size:10px}
 #e_tabs button i{font-style:normal;font-size:20px}
}
.lgrid{display:grid;grid-template-columns:repeat(3,1fr);gap:8px}
.lc{display:flex;flex-direction:column;align-items:center;gap:5px;padding:8px 4px;border-radius:12px;background:var(--card2);border:2px solid var(--line);color:var(--tx);font-size:11px;font-weight:700}
.lc.on{border-color:var(--ac)}
@media(max-width:900px){
 .modal.editfs>div{display:flex;flex-direction:column;overflow:hidden;padding:8px 10px 0}
 .modal.editfs .big{flex:1;min-height:0;display:flex!important;flex-direction:column;gap:6px}
 .modal.editfs .big>div:first-child{position:static;flex:0 0 auto;padding:0}
 .modal.editfs #e_stage{height:38vh;width:auto;aspect-ratio:9/16;max-width:100%;margin:0 auto}
 .modal.editfs .big>div:last-child{flex:1;min-height:0;overflow:auto;background:var(--card);border-radius:20px 20px 0 0;padding:12px 12px 90px}
}
</style>
</head>
<body>
<div id="bgfx"></div>
<div class="scrim" id="scrim"></div>
<div class="app">
<aside class="side" id="side">
  <div class="brand"><div class="lg">▶</div><div>Lico Clips<small>clips virales con IA</small></div></div>
  <button class="newbtn" id="newbtn">＋ Nuevo stream</button>
  <h6>ESTUDIO</h6>
  <button class="it on" data-t="home"><span class="ic">🏠</span>Inicio</button>
  <button class="it" data-t="streams"><span class="ic">📡</span>Streams</button>
  <button class="it" data-t="clips"><span class="ic">🎬</span>Clips</button>
  <h6>DISTRIBUCIÓN</h6>
  <button class="it" data-t="cal"><span class="ic">🗓️</span>Calendario</button>
  <button class="it" data-t="cola"><span class="ic">📤</span>Cola<span class="badge hide" id="qb">0</span></button>
  <button class="it" data-t="ana"><span class="ic">📈</span>Analíticas</button>
  <button class="it" data-t="agent"><span class="ic">✨</span>Agente IA</button>
  <h6>AJUSTES</h6>
  <button class="it" data-t="acc"><span class="ic">🔗</span>Creadores</button>
  <button class="it" data-t="me"><span class="ic">⚙️</span>Mi cuenta</button>
  <div class="sys"><div><span class="dot"></span><b>Sistema en línea</b></div><div id="sysbadges" style="margin-top:6px"></div></div>
</aside>
<main class="main">
<div class="top"><button id="menubtn">☰</button><b>Lico Clips</b></div>

<!-- ===================== INICIO ===================== -->
<section id="p-home">
  <div class="hero"><h2>Convierte tus directos en clips virales</h2>
    <div class="sub">Pega el VOD (o la ruta del video). La IA busca los mejores momentos y los edita sola: cámara, subtítulos, título y más. Después tocas <b>Editar</b> en el clip que quieras cambiar.</div>
    <div class="row" style="margin-top:12px"><button class="btn lg grow" id="homego">＋ Nuevo stream</button></div></div>
  <div class="stats"><div class="stat"><b id="s_clips">0</b><span>Clips generados</span></div><div class="stat"><b id="s_pub">0</b><span>Publicados</span></div>
    <div class="stat"><b id="s_wait">0</b><span>En cola</span></div><div class="stat"><b id="s_jobs">0</b><span>Streams</span></div></div>
  <h2>🔥 Tus mejores clips</h2>
  <div class="rail" id="toprail"><div class="sub">Todavía no hay clips.</div></div>
</section>

<!-- ===================== STREAMS ===================== -->
<section id="p-streams" class="hide">
  <div class="row"><h2 class="grow" style="margin:0">Streams</h2><button class="btn sm" id="streamnew">＋ Nuevo stream</button></div>
  <div class="card" style="margin-top:10px"><div id="jobs" class="sub">Cargando…</div></div>
</section>

<!-- ===================== NUEVO STREAM ===================== -->
<section id="p-new" class="hide">
  <div id="warns"></div>
  <div class="card">
    <h2>Nuevo stream</h2>
    <label>Link del VOD (Kick, Twitch, YouTube…)</label>
    <input type="url" id="url" placeholder="https://kick.com/…/videos/…" autocomplete="off">
    <label>…o la ruta de un video que ya está en tu celular (ideal para directos de 6-8 horas, no se copia)</label>
    <input type="text" id="lpath" placeholder="/sdcard/Download/directo.mp4" autocomplete="off">
    <label>…o súbelo desde el navegador (para videos muy grandes mejor usa la ruta)</label>
    <input type="file" id="file" accept="video/*">
    <div class="bar hide" id="upbar"><i></i></div>
    <div class="chk" style="margin-top:14px"><input type="checkbox" id="n_mute"><span><b>🤐 Tapar groserías</b> — silencia solo la palabra (de su inicio a su final), no todo el video. Necesita la clave de OpenAI.</span></div>
    <label>Plantilla de estilo</label><select id="n_tpl"><option value="">Sin plantilla (estilo por defecto)</option></select>
    <details><summary>Rango y cantidad (opcional)</summary>
      <div class="g2"><div><label>Desde (h:mm:ss)</label><input type="text" id="tfrom" placeholder="0:00"></div>
      <div><label>Hasta</label><input type="text" id="tto" placeholder="fin"></div></div>
      <div class="g2"><div><label>Cuántos clips</label><input type="number" id="nclips" value="15" min="1" max="30"></div>
      <div><label>Duración (seg)</label><input type="number" id="cliplen" value="40" min="10" max="120"></div></div>
    </details>
    <details><summary>Diseño de los clips (se puede cambiar clip por clip después)</summary><div id="set-new"></div></details>
    <div class="row" style="margin-top:12px"><button class="btn lg grow" id="go">Buscar momentos y crear clips</button></div>
    <div id="newerr"></div>
  </div>
</section>

<!-- ===================== CLIPS ===================== -->
<section id="p-clips" class="hide">
  <div class="card" id="jhead"><div class="sub">Elige un stream en “Streams”.</div></div>
  <div id="jready" class="hide">
    <div class="tools">
      <button class="fchip on" data-f="all">Todos</button>
      <button class="fchip" data-f="risas">😂 Risas</button><button class="fchip" data-f="terror">😱 Terror</button><button class="fchip" data-f="polemica">🔥 Polémica</button>
      <button class="fchip" data-f="epico">🏆 Épico</button><button class="fchip" data-f="fail">🤦 Fail</button><button class="fchip" data-f="otro">Otros</button>
      <select id="sortsel" style="width:auto"><option value="score">Mejor nota primero</option><option value="time">Orden del directo</option><option value="dur">Más largos</option></select>
      <span style="flex:1"></span>
      <button class="btn sec sm" id="selall">Elegir todos</button><button class="btn sm" id="pubsel">Publicar elegidos</button>
    </div>
    <div id="clips"></div>
    <h2 style="margin-top:22px">Ajustes del stream</h2>
    <div class="card" id="campanel"></div>
    <div class="card"><h2>Diseño y ajustes de todos los clips</h2><div id="set-job"></div>
      <div class="row" style="margin-top:10px"><button class="btn sec grow" id="gov">🖼️ Textos e imágenes de todos los clips</button><button class="btn grow" id="rerender">Guardar y rehacer todos</button></div>
      <div class="tiny" id="reinfo"></div></div>
  </div>
</section>

<!-- ===================== CALENDARIO ===================== -->
<section id="p-cal" class="hide">
  <div class="row"><h2 class="grow" style="margin:0">Calendario de publicaciones</h2><button class="btn sec sm" id="calprev">‹</button><b id="calttl"></b><button class="btn sec sm" id="calnext">›</button></div>
  <div class="card" style="margin-top:10px"><div class="cal" id="calgrid"></div></div>
  <div class="card" id="calday"><div class="sub">Toca un día para ver lo que sale ese día.</div></div>
</section>

<!-- ===================== COLA ===================== -->
<section id="p-cola" class="hide">
  <div class="card"><h2>Cola de publicaciones</h2><div class="sub">Las programadas salen solas a su hora (las de Facebook las programa Facebook; las de TikTok salen desde tu celular, así que déjalo con <code>termux-wake-lock</code> y la app abierta).</div></div>
  <div id="queue"></div>
</section>

<!-- ===================== ANALITICAS ===================== -->
<section id="p-ana" class="hide">
  <h2>Analíticas</h2>
  <div class="stats"><div class="stat"><b id="a_found">0</b><span>Momentos hallados</span></div><div class="stat"><b id="a_avg">0</b><span>Nota media /100</span></div>
    <div class="stat"><b id="a_fb">0</b><span>Facebook</span></div><div class="stat"><b id="a_tt">0</b><span>TikTok</span></div></div>
  <div class="card"><h3 style="margin-top:0">Clips por categoría</h3><div id="a_cats"></div></div>
  <div class="card sub">Las vistas y los likes de TikTok/Facebook no se pueden leer sin permisos extra de esas redes; aquí ves lo que genera y publica Lico Clips.</div>
</section>

<!-- ===================== AGENTE IA ===================== -->
<section id="p-agent" class="hide">
  <div class="card"><h2>✨ Agente IA y video de referencia</h2>
    <div class="sub">Dime cómo quieres tus clips o sube un video de referencia: la IA lee su estilo (diseño, marca de agua, textos fijos como “Kick NombreDelCanal”) y lo copia con <b>tu nombre</b>. Necesita una clave de Anthropic válida.</div>
    <label>Tu nombre / canal (reemplaza al de la referencia)</label><input type="text" id="ag_name" placeholder="Ej: LicoGato" maxlength="40">
    <label>Video de referencia (opcional)</label><input type="file" id="ag_file" accept="video/*">
    <label>Instrucciones (prompt)</label><textarea id="ag_prompt" placeholder="Ej: pon mi nombre arriba con el logo de Kick, subtítulos animados, pantalla completa y título en tarjeta blanca"></textarea>
    <div class="row" style="margin-top:10px"><button class="btn grow" id="ag_go">Analizar y crear estilo</button></div><div id="ag_msg"></div>
  </div>
  <div class="card hide" id="ag_res"></div>
</section>

<!-- ===================== CREADORES (cuentas) ===================== -->
<section id="p-acc" class="hide">
  <div class="card" id="acc-fb"></div>
  <div class="card" id="acc-tt"></div>
</section>

<!-- ===================== MI CUENTA ===================== -->
<section id="p-me" class="hide">
  <div class="card"><h2>Apariencia</h2>
    <div class="chk"><input type="checkbox" id="th_light"><span>Modo claro</span></div>
    <div class="chk"><input type="checkbox" id="th_bg"><span>Fondo animado de emojis</span></div>
    <div class="tiny">App instalable: en Chrome toca ⋮ → “Instalar aplicación” o “Agregar a pantalla de inicio”.</div></div>
  <div class="card"><h2>Claves de IA</h2>
    <div class="sub">Sin claves todo funciona con el audio. Con ellas: voz (subtítulos, tapar groserías, mejor elección de momentos) y cámara/títulos con IA.</div>
    <label>Anthropic (Claude, empieza con sk-ant-) <span id="aimask" class="tiny"></span></label><input type="password" id="k_ai" placeholder="sk-ant-…" autocomplete="off">
    <label>OpenAI (Whisper: voz) <span id="sttmask" class="tiny"></span></label><input type="password" id="k_stt" placeholder="sk-…" autocomplete="off">
    <div class="row" style="margin-top:10px"><button class="btn" id="savekeys">Guardar claves</button></div><div id="keymsg"></div></div>
  <div class="card"><h2>Plantillas de estilo</h2><div class="sub">Guarda el diseño completo (subtítulos, título, música, logo, textos) y úsalo en cualquier stream.</div>
    <div id="tpls" style="margin-top:8px"></div>
    <div class="row" style="margin-top:8px"><input type="text" id="tpl_name" placeholder="Nombre de la plantilla" style="flex:1" maxlength="40"><button class="btn sec" id="tpl_save">Guardar ajustes por defecto como plantilla</button></div><div id="tplmsg"></div></div>
  <div class="card"><h2>Ajustes por defecto</h2><div class="sub">Se usan para cada stream nuevo.</div><div id="set-def"></div>
    <div class="row" style="margin-top:10px"><button class="btn grow" id="savedef">Guardar como predeterminados</button></div><div id="defmsg"></div></div>
  <div class="card"><h2>Música, logo e imágenes</h2><div class="sub">Sube canciones (mp3/m4a) o imágenes (png con fondo transparente). Las imágenes se pueden poner encima de los clips en el editor.</div>
    <input type="file" id="assetfile" accept="audio/*,image/*"><div class="row" style="margin-top:8px"><button class="btn sec" id="assetup">Subir</button></div>
    <div id="assets" style="margin-top:8px"></div></div>
  <div class="card"><h2>Estado</h2><div id="status" class="sub"></div></div>
</section>
</main>
</div>

<div class="modal hide" id="modal"><div id="modalbody"></div></div>

<script>
"use strict";
const $=s=>document.querySelector(s), $$=s=>[...document.querySelectorAll(s)];
const esc=s=>String(s??"").replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
async function api(path,opt){
  const o=Object.assign({},opt||{});
  if(o.json!==undefined){o.method=o.method||"POST";o.headers={"Content-Type":"application/json"};o.body=JSON.stringify(o.json);delete o.json}
  const r=await fetch(path,o); let j={}; try{j=await r.json()}catch(e){}
  if(!r.ok) throw new Error(j.error||("Error "+r.status)); return j;
}
const fmtT=s=>{s=Math.max(0,Math.round(s));const h=Math.floor(s/3600),m=Math.floor(s%3600/60),x=s%60;return (h?h+":"+String(m).padStart(2,"0"):m)+":"+String(x).padStart(2,"0")};
const parseT=s=>{s=String(s||"").trim();if(!s)return null;const p=s.replace(",",".").split(":").map(Number);if(p.some(isNaN))return null;return p.reduce((a,b)=>a*60+b,0)};
const CATN={risas:"😂 Risas",terror:"😱 Terror",polemica:"🔥 Polémica",epico:"🏆 Épico",fail:"🤦 Fail",otro:"Momento",susto:"😱 Susto",hype:"🙌 Hype",fuerte:"🔊 Fuerte"};
let TPLS=[],FILT="all",SORT="score",CFG={},ASSETS=[],ACC={},cur=null,JOB=null,pollT=null,edits={},sel=new Set();

/* ---------- pestañas ---------- */
const PAGES=["home","streams","new","clips","cal","cola","ana","agent","acc","me"];
function tab(t){
  if(!PAGES.includes(t))t="home";
  $$("#side .it").forEach(b=>b.classList.toggle("on",b.dataset.t===t||(t==="new"&&b.dataset.t==="streams")));
  PAGES.forEach(x=>$("#p-"+x).classList.toggle("hide",x!==t));
  document.body.classList.remove("menu");
  if(t==="cola")loadQueue(); if(t==="acc")loadAcc(); if(t==="me")loadSettingsTab(); if(t==="streams")loadJobs(); if(t==="home")loadHome();
  if(t==="cal")loadCal(); if(t==="ana")loadAna(); if(t==="new")loadNew();
  if(t==="clips"&&!cur)autoOpenLast();
  try{history.replaceState(null,"","#"+t)}catch(e){}
  window.scrollTo(0,0);
}
$("#side").onclick=e=>{const b=e.target.closest("[data-t]");if(b)tab(b.dataset.t)};
$("#menubtn").onclick=()=>document.body.classList.toggle("menu");
$("#scrim").onclick=()=>document.body.classList.remove("menu");
$("#newbtn").onclick=$("#homego").onclick=$("#streamnew").onclick=()=>tab("new");
async function autoOpenLast(){try{const js=await api("/api/jobs");if(js.length&&!cur)openJob(js[0].id)}catch(e){}}

/* ---------- formulario de ajustes (se usa en 3 sitios) ---------- */
const LAY={dual:"Dos pantallas apiladas (si el video ya trae dos)",auto:"Inteligente (detecta pantalla doble y tu cámara)",fill:"Pantalla completa vertical (recortada, recomendado si tu cámara ocupa todo)",split:"Cámara + gameplay (apilados)",circle:"Gameplay con la cámara en círculo",cam:"Solo la cámara",game:"Solo el gameplay",horizontal:"Horizontal 16:9 (sin recortar)"};
function opts(map,v){return Object.entries(map).map(([k,t])=>`<option value="${esc(k)}"${String(v)===k?" selected":""}>${esc(t)}</option>`).join("")}
function assetOpts(kind,v){return `<option value="">Ninguno</option>`+ASSETS.filter(a=>a.kind===kind).map(a=>`<option value="${esc(a.name)}"${v===a.name?" selected":""}>${esc(a.name)}</option>`).join("")}
function prevBox(s){
  if(s.layout==="split"){const t=s.split_pct;const cam=`<div class="c" style="flex:${t}">CÁMARA</div>`,gm=`<div class="g" style="flex:${100-t}">GAMEPLAY</div>`;return `<div class="prev">${s.cam_order==="top"?cam+gm:gm+cam}</div>`}
  if(s.layout==="circle")return `<div class="prev"><div class="g" style="flex:1">GAMEPLAY</div><span class="dot"></span></div>`;
  if(s.layout==="auto")return `<div class="prev"><div class="g" style="flex:1">INTELIGENTE</div></div>`;
  if(s.layout==="fill")return `<div class="prev"><div class="g" style="flex:1">COMPLETO</div></div>`;
  if(s.layout==="cam")return `<div class="prev"><div class="c" style="flex:1">CÁMARA</div></div>`;
  if(s.layout==="game")return `<div class="prev"><div class="g" style="flex:1">GAMEPLAY</div></div>`;
  return `<div class="prev" style="aspect-ratio:16/9;width:130px"><div class="g" style="flex:1">16:9</div></div>`;
}
function renderSettings(el,s,onchange){
  const id=el.id;
  el.innerHTML=`
  <div class="row" style="align-items:flex-start"><div class="grow">
    <label>Diseño</label><select data-k="layout">${opts(LAY,s.layout)}</select></div><div id="${id}-prev">${prevBox(s)}</div></div>
  <div data-show="split auto"><label>Posición de la cámara</label><select data-k="cam_order">${opts({top:"Cámara ARRIBA, gameplay abajo",bottom:"Cámara abajo, gameplay arriba"},s.cam_order)}</select>
    <label>Alto de la cámara: <b data-v="split_pct">${s.split_pct}</b>% del video</label><input type="range" min="20" max="60" step="1" data-k="split_pct" value="${s.split_pct}"></div>
  <div data-show="circle"><label>Dónde va el círculo</label><select data-k="circle_pos">${opts({br:"Abajo a la derecha",bl:"Abajo a la izquierda",tr:"Arriba a la derecha",tl:"Arriba a la izquierda",bc:"Abajo al centro"},s.circle_pos)}</select></div>
  <div data-show="fill split circle game auto"><div class="tiny" data-show-only="fill">El recorte (zoom y zona) se elige en cada clip con “Editar”.</div><div class="chk"><input type="checkbox" data-k="follow_action" ${s.follow_action?"checked":""}><span>Seguir la acción (el recorte se mueve hacia el movimiento; solo si el recorte está activo)</span></div></div>
  <div data-show="split circle game auto"><label>El gameplay se ve…</label><select data-k="game_fit">${opts({blur:"Completo (con fondo borroso)",crop:"Recortado a pantalla completa"},s.game_fit)}</select>
    <div data-fit="crop"><label>Zona del gameplay: <b data-v="game_x">${s.game_x}</b>% (0=izquierda, 100=derecha)</label><input type="range" min="0" max="100" data-k="game_x" value="${s.game_x}">
    </div></div>
  <div class="g2"><div><label>Resolución</label><select data-k="resolution">${opts({480:"480p",720:"720p",1080:"1080p"},s.resolution)}</select></div>
  <div><label>FPS</label><select data-k="fps">${opts({original:"Original",24:"24",30:"30",60:"60"},s.fps)}</select></div></div>
  <label>Calidad</label><select data-k="quality">${opts({alta:"Alta (archivo grande)",media:"Media",baja:"Baja (archivo chico)"},s.quality)}</select>
  <div class="chk"><input type="checkbox" data-k="zoom_peak" ${s.zoom_peak?"checked":""}><span>Zoom rápido en el momento clave</span></div>
  <div class="chk"><input type="checkbox" data-k="captions" ${s.captions?"checked":""}><span>Subtítulos (necesita clave de OpenAI)</span></div>
  <div data-cap><label>Estilo de subtítulos</label><select data-k="caption_style">${opts({karaoke:"Animados (palabra resaltada)",simple:"Simples"},s.caption_style)}</select></div>
  <div class="chk"><input type="checkbox" data-k="titles" ${s.titles?"checked":""}><span>Mostrar el título arriba</span></div>
  <div class="chk"><input type="checkbox" data-k="normalize" ${s.normalize?"checked":""}><span>Nivelar el volumen</span></div>
  <label>Efecto de sonido en el momento clave</label><select data-k="sfx">${opts({none:"Ninguno",boom:"Boom",whoosh:"Whoosh",ding:"Ding"},s.sfx)}</select>
  <label>Música de fondo</label><select data-k="music">${assetOpts("music",s.music)}</select>
  <div data-music><label>Volumen de la música: <b data-v="music_volume">${Math.round(s.music_volume*100)}</b>%</label><input type="range" min="3" max="60" data-k="music_volume" value="${Math.round(s.music_volume*100)}">
  <div class="chk"><input type="checkbox" data-k="music_duck" ${s.music_duck?"checked":""}><span>Bajar la música cuando hablas</span></div></div>
  <div class="g2"><div><label>Logo</label><select data-k="logo">${assetOpts("logo",s.logo)}</select></div>
  <div><label>Posición del logo</label><select data-k="logo_pos">${opts({tr:"Arriba derecha",tl:"Arriba izquierda",br:"Abajo derecha",bl:"Abajo izquierda"},s.logo_pos)}</select></div></div>
  <label>Texto de intro (2 s, opcional)</label><input type="text" data-k="intro_text" maxlength="80" value="${esc(s.intro_text)}" placeholder="Ej: ¡Mira esto!">
  <label>Texto final (2 s, opcional)</label><input type="text" data-k="outro_text" maxlength="80" value="${esc(s.outro_text)}" placeholder="Ej: Sígueme en Kick">
  <label>Sonido al tapar groserías</label><select data-k="profanity_sound">${opts({mute:"Silencio",beep:"Pitido (beep)",low:"Tono grave"},s.profanity_sound||"mute")}</select>
  <div class="chk"><input type="checkbox" data-k="mute_profanity" ${s.mute_profanity?"checked":""}><span>🤐 Tapar groserías (silencia solo la palabra)</span></div>
  <div class="chk"><input type="checkbox" data-k="auto_create" ${s.auto_create?"checked":""}><span>Crear los clips automáticamente al terminar de analizar</span></div>`;
  const read=()=>{const o={};el.querySelectorAll("[data-k]").forEach(i=>{const k=i.dataset.k;let v=i.type==="checkbox"?i.checked:i.value;
      if(["split_pct","game_x"].includes(k))v=+v; if(k==="music_volume")v=+v/100; o[k]=v});return o};
  const sync=()=>{const s2=read();
    el.querySelectorAll("[data-show]").forEach(d=>d.classList.toggle("hide",!d.dataset.show.split(" ").includes(s2.layout)));
    el.querySelectorAll("[data-fit]").forEach(d=>d.classList.toggle("hide",s2.game_fit!=="crop"));
    el.querySelectorAll("[data-cap]").forEach(d=>d.classList.toggle("hide",!s2.captions));
    el.querySelectorAll("[data-music]").forEach(d=>d.classList.toggle("hide",!s2.music));
    el.querySelectorAll("[data-v]").forEach(b=>{const k=b.dataset.v;b.textContent=k==="music_volume"?Math.round(s2[k]*100):s2[k]});
    const pb=$("#"+id+"-prev");if(pb)pb.innerHTML=prevBox(s2);
    if(onchange)onchange(s2)};
  el._ov=JSON.parse(JSON.stringify(s.overlays||[])); el.oninput=sync; el.onchange=sync; el.getSettings=()=>Object.assign(read(),{overlays:el._ov}); sync();
}

/* ---------- Crear ---------- */
async function boot(){
  initLook();
  CFG=await api("/api/config"); ASSETS=await api("/api/assets");
  renderSettings($("#set-new"),CFG.defaults);
  sysBadges();
  const h=(location.hash||"").slice(1); tab(PAGES.includes(h)&&h!=="clips"?h:"home");
  setInterval(()=>{if(!$("#p-cola").classList.contains("hide"))loadQueue(); else refreshBadge()},8000); refreshBadge();
}
function sysBadges(){
  $("#sysbadges").innerHTML=[["IA",CFG.ai],["Voz",CFG.stt],["FFmpeg",CFG.ffmpeg]].map(([n,v])=>`<span class="chipx${v?"":" off"}">${v?"✓":"✕"} ${n}</span>`).join("");
}
function initLook(){
  let th="dark",bg="1";try{th=localStorage.getItem("lc_theme")||"dark";bg=localStorage.getItem("lc_bg")||"1"}catch(e){}
  document.documentElement.dataset.theme=th;
  const fx=$("#bgfx");fx.innerHTML="";
  if(bg==="1"){const em=["🎬","🎥","📹","🎞️","▶️","⭐","🔥","😂","🎮","🏆","✂️","🎧"];
    for(let i=0;i<16;i++){const sp=document.createElement("span");sp.textContent=em[i%em.length];sp.style.left=(Math.random()*96)+"%";sp.style.fontSize=(22+Math.random()*30)+"px";sp.style.animationDuration=(18+Math.random()*26)+"s";sp.style.animationDelay=(-Math.random()*40)+"s";fx.appendChild(sp)}}
  const a=$("#th_light"),b=$("#th_bg");if(a){a.checked=th==="light";b.checked=bg==="1"}
}
$("#th_light").onchange=e=>{try{localStorage.setItem("lc_theme",e.target.checked?"light":"dark")}catch(x){}initLook()};
$("#th_bg").onchange=e=>{try{localStorage.setItem("lc_bg",e.target.checked?"1":"0")}catch(x){}initLook()};
if("serviceWorker" in navigator){try{navigator.serviceWorker.register("/sw.js").catch(()=>{})}catch(e){}}
async function loadNew(){
  const w=[];
  if(!CFG.ffmpeg)w.push(["bad","Falta FFmpeg: <code>pkg install ffmpeg</code>"]);
  if(!CFG.ytdlp)w.push(["warn","Falta yt-dlp para bajar VODs por link: <code>pip install yt-dlp</code> (o sube el video)"]);
  else if(!CFG.impers)w.push(["warn","Para Kick instala también <code>pip install \"yt-dlp[default,curl-cffi]\"</code>. Si no se deja, sube el video."]);
  $("#warns").innerHTML=w.map(([c,t])=>`<div class="msg ${c}">${t}</div>`).join("");
  try{TPLS=await api("/api/templates")}catch(e){TPLS=[]}
  $("#n_tpl").innerHTML='<option value="">Sin plantilla (estilo por defecto)</option>'+TPLS.map(t=>`<option value="${esc(t.id)}">${esc(t.name)}</option>`).join("");
  $("#n_mute").checked=!!(CFG.defaults&&CFG.defaults.mute_profanity);
}
$("#n_tpl").onchange=e=>{const t=TPLS.find(x=>x.id===e.target.value);renderSettings($("#set-new"),t?t.settings:CFG.defaults);$("#n_mute").checked=!!(t?t.settings.mute_profanity:(CFG.defaults||{}).mute_profanity)};
async function loadJobs(){
  try{const js=await api("/api/jobs"); $("#jobs").innerHTML=js.length?js.map(j=>`<div class="q" style="margin:8px 0"><div><b>${esc(j.label||j.id)}</b><div class="tiny">${new Date(j.created*1000).toLocaleString()} · ${esc({ready:"listo",running:"analizando…",queued:"en cola",error:"error",cancelled:"cancelado"}[j.status]||j.status)} · ${j.clips} momentos · ${j.done}/${j.exports} clips hechos</div></div><button class="btn sec sm" data-open="${j.id}">Abrir</button></div>`).join(""):"Todavía no hay trabajos."}catch(e){}
}
async function loadHome(){
  loadJobs();
  try{const h=await api("/api/home");$("#s_jobs").textContent=h.jobs;$("#s_clips").textContent=h.clips;$("#s_wait").textContent=h.waiting;$("#s_pub").textContent=h.published;
    $("#toprail").innerHTML=h.top.length?h.top.map((c,k)=>`<div class="cc" data-job="${esc(c.job)}"><div class="vid" style="background-image:url('${esc(c.thumb)}')"><span class="rk">#${k+1}</span><span class="sc${c.score>=75?" hi":c.score<45?" lo":""}">${c.score}</span><span class="du">${c.dur}s</span>${c.clip?"":`<div class="cap">${esc(c.title||"Momento")}</div>`}</div>
      <div class="bd"><span class="pill ${esc(c.cat)}">${esc(CATN[c.cat]||c.cat)}</span><div class="ttl">${esc(c.title||"Momento")}</div><button class="btn sm" data-open="${esc(c.job)}">Abrir</button></div></div>`).join(""):'<div class="sub">Todavía no hay clips. Toca “Nuevo stream”.</div>'}catch(e){}
}
$("#toprail").onclick=e=>{const b=e.target.closest("[data-open]");if(b)openJob(b.dataset.open)};
$("#jobs").onclick=e=>{const b=e.target.closest("[data-open]");if(b)openJob(b.dataset.open)};
$("#go").onclick=()=>{
  const fd=new FormData(),url=$("#url").value.trim(),f=$("#file").files[0],lp=$("#lpath").value.trim();
  $("#newerr").innerHTML="";
  if(!url&&!f&&!lp){$("#newerr").innerHTML='<div class="msg bad">Pega un link, escribe la ruta del video o súbelo.</div>';return}
  fd.append("url",url); fd.append("path",lp); if(!url&&!lp&&f)fd.append("file",f);
  fd.append("t_from",$("#tfrom").value);fd.append("t_to",$("#tto").value);fd.append("n_clips",$("#nclips").value);fd.append("clip_len",$("#cliplen").value);
  const ns=$("#set-new").getSettings();ns.mute_profanity=$("#n_mute").checked;fd.append("settings",JSON.stringify(ns));
  const btn=$("#go"),bar=$("#upbar");btn.disabled=true;btn.textContent="Enviando…";
  const done=()=>{btn.disabled=false;btn.textContent="Buscar momentos y crear clips";bar.classList.add("hide")};
  const x=new XMLHttpRequest();x.open("POST","/api/analyze");
  if(f&&!url&&!lp){bar.classList.remove("hide");x.upload.onprogress=e=>{if(e.lengthComputable){bar.firstElementChild.style.width=(100*e.loaded/e.total)+"%";btn.textContent="Subiendo… "+Math.round(100*e.loaded/e.total)+"%"}}}
  x.onload=()=>{let j={};try{j=JSON.parse(x.responseText)}catch(e){}done();if(x.status===200)openJob(j.id);else $("#newerr").innerHTML=`<div class="msg bad">${esc(j.error||("Error "+x.status))}</div>`};
  x.onerror=()=>{done();$("#newerr").innerHTML='<div class="msg bad">Se cortó la subida. Para videos grandes usa la ruta del archivo en vez de subirlo.</div>'};
  x.send(fd);
};

/* ---------- Trabajo ---------- */
function openJob(id){cur=id;JOB=null;edits={};$("#clips").innerHTML="";$("#clips").classList.remove("grid");sel=new Set();tab("clips");$("#jready").classList.add("hide");$("#jhead").innerHTML="Cargando…";poll(true)}
async function poll(force){
  clearTimeout(pollT); if(!cur)return;
  try{const j=await api("/api/job/"+cur); const prev=JOB; JOB=j; renderJob(prev,force)}catch(e){$("#jhead").innerHTML=`<div class="msg bad">${esc(e.message)}</div>`;return}
  const busy=JOB.status==="queued"||JOB.status==="running"||JOB.exports.some(x=>x.status==="queued"||x.status==="running");
  pollT=setTimeout(poll,busy?1500:6000);
}
function renderJob(prev,force){
  const j=JOB;
  let h=`<div class="row"><h2 class="grow" style="margin:0">${esc(j.label||"Trabajo")}</h2><button class="btn bad sm" id="deljob">Borrar</button></div>`;
  if(j.status==="queued"||j.status==="running"){
    h+=`<div class="sub">${esc(j.stage)}</div><div class="bar"><i style="width:${j.progress}%"></i></div><div class="row"><span class="tiny grow">${j.progress}%</span><button class="btn sec sm" id="canceljob">Cancelar</button></div>`;
  }else if(j.status==="error"){h+=`<div class="msg bad">${esc(j.error)}</div>`}
  else if(j.status==="cancelled"){h+=`<div class="msg warn">Cancelado.</div>`}
  else{h+=`<div class="sub">${j.clips.length} momentos${j.ai?" · revisados con IA":""} · video de ${fmtT(j.meta.duration)}</div>`}
  $("#jhead").innerHTML=h;
  if(j.log.length&&j.status!=="ready")$("#jhead").innerHTML+=`<div class="tiny" style="margin-top:8px">${j.log.slice(-4).map(esc).join("<br>")}</div>`;
  const ready=j.status==="ready"; $("#jready").classList.toggle("hide",!ready);
  if(!ready)return;
  if(!prev||prev.status!=="ready"){renderCam();renderSettings($("#set-job"),j.settings);}
  renderClips();
}
$("#jhead").onclick=async e=>{
  if(e.target.id==="canceljob")await api("/api/cancel/"+cur,{method:"POST"});
  if(e.target.id==="deljob"&&confirm("¿Borrar este trabajo y todos sus clips?")){
    try{await api("/api/job/"+cur,{method:"DELETE"});cur=null;tab("streams")}catch(er){alert(er.message)}}
};

/* --- cámara --- */
function renderCam(){
  const j=JOB,fc=j.facecam||{x:.74,y:.6,w:.25,h:.37};
  const srcTxt={ia:"detectada con IA ✓",auto:"detectada automáticamente (revísala)",guess:"NO la encontré: mueve el cuadro sobre tu cámara",manual:"marcada por ti ✓"}[j.facecam_src]||"";
  $("#campanel").innerHTML=`<h2>Tu cámara</h2><div class="sub">${esc(srcTxt)}</div>
  ${camBig(j)?'<div class="msg warn">El cuadro cubre casi todo el video. Si tu cámara es la pantalla completa, usa el diseño “Pantalla completa vertical” (abajo, o por clip con “Editar”).</div>':""}
  ${j.facecam_src==="guess"||j.facecam_src==="auto"?'<div class="msg warn">Revisa que el cuadro esté sobre tu cámara. Si lo mueves, pulsa “Guardar cámara” y rehago los clips.</div>':""}
  <div class="camwrap" id="camwrap"><img src="/api/file/${j.id}/facecam_frame.jpg?${Date.now()}" id="camimg" draggable="false"><div class="camrect" id="camrect"><i></i></div></div>
  <div class="row"><button class="btn sm" id="camsave">Guardar cámara</button>
  <button class="btn sec sm" data-corner="tl">↖</button><button class="btn sec sm" data-corner="tr">↗</button><button class="btn sec sm" data-corner="bl">↙</button><button class="btn sec sm" data-corner="br">↘</button>
  <button class="btn sec sm" id="camai">Detectar con IA</button></div><div id="cammsg"></div>`;
  const wrap=$("#camwrap"),rect=$("#camrect"); let box={...fc};
  const draw=()=>{rect.style.left=box.x*100+"%";rect.style.top=box.y*100+"%";rect.style.width=box.w*100+"%";rect.style.height=box.h*100+"%"}; draw();
  let mode=null,st=null;
  rect.onpointerdown=e=>{mode=e.target.tagName==="I"?"rs":"mv";st={x:e.clientX,y:e.clientY,b:{...box}};rect.setPointerCapture(e.pointerId);e.preventDefault()};
  rect.onpointermove=e=>{if(!mode)return;const r=wrap.getBoundingClientRect(),dx=(e.clientX-st.x)/r.width,dy=(e.clientY-st.y)/r.height;
    if(mode==="mv"){box.x=Math.min(1-box.w,Math.max(0,st.b.x+dx));box.y=Math.min(1-box.h,Math.max(0,st.b.y+dy))}
    else{box.w=Math.min(1-box.x,Math.max(.05,st.b.w+dx));box.h=Math.min(1-box.y,Math.max(.05,st.b.h+dy))}draw()};
  rect.onpointerup=()=>{mode=null};
  $$("[data-corner]").forEach(b=>b.onclick=()=>{const c=b.dataset.corner;box.x=c[1]==="l"?0.01:1-box.w-0.01;box.y=c[0]==="t"?0.02:1-box.h-0.02;draw()});
  $("#camsave").onclick=async()=>{try{await api("/api/facecam/"+cur,{json:box});$("#cammsg").innerHTML='<div class="msg ok">Cámara guardada.</div>';if(JOB.exports.length&&confirm("¿Rehacer todos los clips con esta cámara?"))await makeClips(JOB.clips.map(c=>c.i));poll(true)}catch(e){$("#cammsg").innerHTML=`<div class="msg bad">${esc(e.message)}</div>`}};
  $("#camai").onclick=async()=>{$("#cammsg").innerHTML='<div class="sub">Buscando tu cámara…</div>';try{const r=await api("/api/facecam/"+cur+"/detect",{method:"POST"});box={...r.facecam};draw();$("#cammsg").innerHTML='<div class="msg ok">¡Encontrada! Revisa el cuadro y guarda.</div>'}catch(e){$("#cammsg").innerHTML=`<div class="msg bad">${esc(e.message)}</div>`}};
}

/* --- clips (tarjetas con clave: el <video> se crea una sola vez y NO se vuelve a tocar en cada consulta) --- */
function clipEdit(c){return edits[c.i]||(edits[c.i]={title:c.title||"",start:c.start,end:c.end,layout:c.layout||"",
  cx:c.cx==null?.5:c.cx,cy:c.cy==null?.5:c.cy,zoom:c.zoom||1,title_on:c.title_on==null?!!(JOB.settings&&JOB.settings.titles):!!c.title_on,
  overlays:JSON.parse(JSON.stringify(c.overlays||[])),cap_lines:JSON.parse(JSON.stringify(c.cap_lines||[])),bg:JSON.parse(JSON.stringify(c.bg||{mode:"none"})),cap_for:(c.cap_lines&&c.cap_lines.length)?[c.start,c.end]:null})}
function exportsOf(i){return JOB.exports.filter(e=>e.i===i).sort((a,b)=>b.n-a.n)}
const etaTxt=s=>s==null?"":(s>=60?" · faltan ~"+Math.ceil(s/60)+" min":" · faltan ~"+Math.max(5,s)+" s");
const scoreOf=c=>Math.round((c.intensity||0)*10);
function camBig(j){const f=j.facecam;return !!f&&f.w*f.h>0.42}
function cardHTML(c){return `<div class="cc" data-i="${c.i}"><div class="vid" data-vid><span class="rk"></span><span class="sc"></span><span class="du"></span><div class="cap hide"></div><div class="ov hide" data-ov></div></div>
  <div class="bd"><div class="row" style="gap:6px"><input type="checkbox" data-sel style="width:18px;height:18px;accent-color:var(--ac)"><span class="pill" data-chip></span></div><div class="ttl" data-ttl></div><div class="tiny" data-why style="line-height:1.25"></div><div class="acts" data-acts></div></div></div>`}
function syncCard(card,c,rank){
  const j=JOB,last=exportsOf(c.i)[0],vid=card.querySelector("[data-vid]");
  card.querySelector(".rk").textContent="#"+rank;
  const sc=card.querySelector(".sc");sc.textContent=scoreOf(c);sc.className="sc"+(scoreOf(c)>=75?" hi":scoreOf(c)<45?" lo":"");
  card.querySelector(".du").textContent=Math.round(c.end-c.start)+"s";
  const ch=card.querySelector("[data-chip]");ch.textContent=CATN[c.cat]||c.cat;ch.className="pill "+c.cat;
  card.querySelector("[data-why]").textContent=c.why||"";card.title=c.why||"";const t=(c.title||"").trim()||"Momento";card.querySelector("[data-ttl]").textContent=t;
  const cap=card.querySelector(".cap");cap.textContent=t;
  if(!vid.style.backgroundImage&&c.thumb)vid.style.backgroundImage=`url('${c.thumb}')`;
  const done=last&&last.status==="done",busy=last&&(last.status==="queued"||last.status==="running");
  // video: solo se crea/cambia si cambia el número de exportación
  let v=vid.querySelector("video");
  if(done){ if(!v||v.dataset.n!=last.n){ if(v)v.remove(); v=document.createElement("video");v.controls=true;v.playsInline=true;v.preload="metadata";v.dataset.n=last.n;v.src=`/clipfile/${j.id}/${last.n}`;v.poster=c.thumb||"";vid.insertBefore(v,vid.firstChild)} }
  else if(v&&!busy){v.remove()}
  cap.classList.toggle("hide",!!done||!!busy);
  vid.querySelectorAll(".rk,.sc,.du").forEach(x=>x.style.display=(done&&v&&!v.paused)?"none":"");
  // capa de estado
  const ov=card.querySelector("[data-ov]");
  if(busy){ov.classList.remove("hide");
    let b=ov.querySelector(".bar");
    if(!b){ov.innerHTML=`<div class="tiny" data-st></div><div class="bar"><i></i></div><div class="tiny" data-pc></div>`}
    ov.querySelector("[data-st]").textContent=last.stage||"Creando…";ov.querySelector(".bar>i").style.width=last.progress+"%";ov.querySelector("[data-pc]").textContent=last.progress+"%"+etaTxt(last.eta)}
  else if(last&&last.status==="error"){ov.classList.remove("hide");ov.innerHTML=`<div class="tiny" style="color:#ffb3bd">${esc(last.error||"Error")}</div>`}
  else{ov.classList.add("hide");ov.innerHTML=""}
  // botones: solo si cambia el estado
  const key=(last?last.status+last.n:"none"),acts=card.querySelector("[data-acts]");
  if(acts.dataset.k!==key){acts.dataset.k=key;
    acts.innerHTML=`<button class="btn sm" data-act="edit">✏️ Editar</button>`+
      (done?`<a class="btn sec sm" href="/clipfile/${j.id}/${last.n}?dl=1" style="text-decoration:none;text-align:center">⬇️</a><button class="btn ok sm" data-act="pub">Publicar</button>`:"")+
      (busy?`<button class="btn bad sm" data-act="cancel">Parar</button>`:"")+
      (!last||last.status==="error"||last.status==="cancelled"?`<button class="btn sec sm" data-act="make">Crear</button>`:"")}
}
function renderClips(){
  const j=JOB,box=$("#clips");
  const byScore=[...j.clips].sort((a,b)=>(b.intensity||0)-(a.intensity||0));
  const rank={};byScore.forEach((c,k)=>rank[c.i]=k+1);
  let order=byScore;
  if(SORT==="time")order=[...j.clips].sort((a,b)=>a.start-b.start);
  if(SORT==="dur")order=[...j.clips].sort((a,b)=>(b.end-b.start)-(a.end-a.start));
  if(!box.classList.contains("grid"))box.classList.add("grid");
  if(!j.clips.length){box.classList.remove("grid");box.innerHTML=`<div class="card sub">No encontré momentos claros. Prueba con otro rango o más clips.</div>`;return}
  if(box.querySelector(":scope > .card"))box.innerHTML="";
  const have=new Set([...box.children].map(x=>+x.dataset.i));
  order.forEach(c=>{if(!have.has(c.i)){const d=document.createElement("div");d.innerHTML=cardHTML(c);const el=d.firstElementChild;el.querySelector("[data-sel]").checked=sel.has(c.i);box.appendChild(el)}});
  order.forEach((c,k)=>{const card=box.querySelector(`[data-i="${c.i}"]`);if(card){syncCard(card,c,rank[c.i]);card.classList.toggle("hide",FILT!=="all"&&CATGRP(c.cat)!==FILT);if(box.children[k]!==card)box.insertBefore(card,box.children[k]||null)}});
  if(!$("#modal").classList.contains("hide")&&EDI)syncEditor();
}
$("#clips").addEventListener("change",e=>{
  const card=e.target.closest("[data-i]");if(!card)return;const i=+card.dataset.i;
  if(e.target.dataset.sel!==undefined){e.target.checked?sel.add(i):sel.delete(i)}
});
$("#clips").addEventListener("click",async e=>{
  const card=e.target.closest("[data-i]");if(!card)return;const i=+card.dataset.i;
  const act=e.target.dataset.act;if(!act)return;
  const last=exportsOf(i)[0];
  if(act==="edit"){openEditor(i);return}
  if(act==="make")await makeClips([i]);
  if(act==="cancel"&&last)await api(`/api/export/${JOB.id}/${last.n}/cancel`,{method:"POST"});
  if(act==="pub"&&last)openPublish([i]);
  poll(true);
});
async function makeClips(ids,settings){
  const clips=ids.map(i=>{const ed=clipEdit(JOB.clips.find(c=>c.i===i));return {i,title:ed.title,start:ed.start,end:ed.end,layout:ed.layout,cx:ed.cx,cy:ed.cy,zoom:ed.zoom,title_on:ed.title_on,overlays:ed.overlays,bg:ed.bg,cap_lines:ed.cap_lines}});
  try{await api("/api/export/"+cur,{json:{clips,settings:settings||$("#set-job").getSettings()}})}catch(e){alert(e.message)}
}
$("#rerender").onclick=async()=>{
  if(!JOB.clips.length)return;
  try{await api("/api/settings/"+cur,{json:$("#set-job").getSettings()})}catch(e){}
  $("#reinfo").textContent="Rehaciendo todos los clips…";
  await makeClips(JOB.clips.map(c=>c.i)); poll(true);
};
$("#selall").onclick=()=>{const all=JOB.clips.every(c=>sel.has(c.i));sel=new Set(all?[]:JOB.clips.map(c=>c.i));$$("#clips [data-sel]").forEach(b=>b.checked=!all);$("#selall").textContent=all?"Elegir todos":"Quitar todos"};
$("#pubsel").onclick=()=>{const ids=[...sel].filter(i=>exportsOf(i).some(e=>e.status==="done"));if(!ids.length){alert("Elige clips que ya estén creados.");return}openPublish(ids)};
async function shareClip(ex){
  try{const r=await fetch(`/clipfile/${JOB.id}/${ex.n}`);const b=await r.blob();const f=new File([b],(ex.title||"clip").replace(/[^\w-]+/g,"_")+".mp4",{type:"video/mp4"});
    if(navigator.canShare&&navigator.canShare({files:[f]}))await navigator.share({files:[f],title:ex.title||"Clip"});
    else alert("Tu navegador no deja compartir archivos directo. Usa Descargar y súbelo desde la app.")}catch(e){if(e.name!=="AbortError")alert("No pude compartir: "+e.message)}
}

/* --- editor de cada clip (estilo CapCut: textos, imágenes, subtítulos, encuadre, tiempo) --- */
let EDI=null,EDT=0,EDTAB="ov",EDSHOWVID=false;
const LAYASKED={};
const LM={fill:'<i style="flex:1;background:#38bdf8"></i>',split:'<i style="flex:0 0 38%;background:#f0abfc"></i><i style="flex:1;background:#38bdf8"></i>',circle:'<i style="flex:1;background:#38bdf8"></i><b style="position:absolute;right:6px;top:8px;width:18px;height:18px;border-radius:50%;background:#f0abfc"></b>',cam:'<i style="flex:1;background:#f0abfc"></i>',game:'<i style="flex:1;background:#38bdf8"></i>',horizontal:'<i style="flex:0 0 30%;margin:auto 0;background:#38bdf8"></i>',dual:'<i style="flex:1;background:#38bdf8"></i><i style="flex:1;background:#7dd3fc"></i>',auto:'<i style="flex:1;background:linear-gradient(#38bdf8,#f0abfc)"></i>',"":'<i style="flex:1;background:#475569"></i>'};
const layMini=k=>`<span style="display:flex;flex-direction:column;position:relative;width:46px;height:82px;border-radius:7px;overflow:hidden;gap:2px;pointer-events:none">${LM[k]||""}</span>`;
const LAYB={"":"Igual que el resto",auto:"Inteligente",fill:"Pantalla completa vertical",split:"Cámara arriba + gameplay",circle:"Cámara en círculo",cam:"Solo cámara",game:"Solo gameplay",horizontal:"Horizontal 16:9",dual:"Dos pantallas apiladas"};
function effLayout(ed){return ed.layout||(JOB.settings&&JOB.settings.layout)||"auto"}
function ovCss(o,W){
  if(o.type==="image")return "";
  const fs=Math.max(8,o.size*W);let st=`font-size:${fs}px;color:#${o.color};`;
  if(o.bg==="card")st+="background:#fff;color:#111;padding:4px 9px;";
  else if(o.bg==="box")st+="background:#000a;padding:3px 8px;";
  else if(o.bg==="outline")st+="-webkit-text-stroke:"+Math.max(1,fs/14)+"px #000;paint-order:stroke fill;text-shadow:2px 2px 0 #000a;";
  return st;
}
/* editor de textos/imágenes sobre una vista 9:16. list = arreglo que se modifica en sitio */
function mountOv(stage,panel,list,onchange){
  let selI=list.length?0:-1,drag=null;
  const W=()=>stage.clientWidth||300;
  const draw=()=>{
    stage.querySelectorAll(".ov").forEach(x=>x.remove());
    list.forEach((o,k)=>{const d=document.createElement("div");d.className="ov"+(k===selI?" sel":"");d.dataset.k=k;d.style.left=o.x*100+"%";d.style.top=o.y*100+"%";
      if(o.type==="image"){d.style.width=o.size*100+"%";d.style.padding="0";d.innerHTML=`<img src="/assets/${encodeURIComponent(o.asset)}" draggable="false">`}
      else{d.textContent=o.text;d.style.cssText+=ovCss(o,W())}
      stage.appendChild(d)});
    drawPanel();
  };
  const drawPanel=()=>{
    const imgs=ASSETS.filter(a=>a.kind==="logo");
    const o=list[selI];
    panel.innerHTML=`<div class="row"><button class="btn sm" data-ova="text">＋ Texto</button>
      <select data-ovimg style="width:auto;flex:1;min-width:120px"><option value="">＋ Imagen / logo…</option>${imgs.map(a=>`<option value="${esc(a.name)}">${esc(a.name)}</option>`).join("")}</select></div>
      ${imgs.length?"":'<div class="tiny">Para poner imágenes súbelas en Mi cuenta → Música, logo e imágenes.</div>'}
      <div style="margin-top:6px">${list.map((x,k)=>`<div class="ovrow${k===selI?" sel":""}" data-ovk="${k}"><span>${x.type==="image"?"🖼️":"🔤"}</span><span class="nm">${esc(x.type==="image"?x.asset:x.text)}</span><button class="btn bad sm" data-ovdel="${k}">✕</button></div>`).join("")||'<div class="tiny">Todavía no hay textos ni imágenes. Toca “＋ Texto”. Arrástralos sobre el video para moverlos.</div>'}</div>
      ${o?`<div style="margin-top:8px">${o.type==="text"?`<label>Texto</label><input type="text" data-ovp="text" value="${esc(o.text)}" maxlength="100">
        <div class="g2"><div><label>Color</label><input type="color" data-ovp="color" value="#${o.color}" style="width:100%;height:40px;padding:2px"></div>
        <div><label>Fondo</label><select data-ovp="bg">${opts({outline:"Contorno negro",card:"Tarjeta blanca",box:"Caja oscura",none:"Sin fondo"},o.bg)}</select></div></div>`:""}
        <label>Tamaño</label><input type="range" min="${o.type==="text"?2.5:4}" max="${o.type==="text"?15:100}" step="0.5" data-ovp="size" value="${o.type==="text"?o.size*100:o.size*100}">
        <div class="g2"><div><label>Aparece en (seg)</label><input type="number" min="0" step="0.5" data-ovp="t0" value="${o.t0}"></div>
        <div><label>Desaparece en (vacío = hasta el final)</label><input type="number" min="0" step="0.5" data-ovp="t1" value="${o.t1<0?"":o.t1}"></div></div></div>`:""}`;
  };
  panel.onclick=e=>{
    const k=e.target.closest("[data-ovdel]");if(k){list.splice(+k.dataset.ovdel,1);selI=Math.min(selI,list.length-1);draw();onchange&&onchange();return}
    const r=e.target.closest("[data-ovk]");if(r){selI=+r.dataset.ovk;draw();return}
    if(e.target.dataset.ova==="text"){list.push({type:"text",text:"Tu texto",x:.5,y:.12,size:.07,color:"ffffff",bg:"outline",t0:0,t1:-1});selI=list.length-1;draw();onchange&&onchange()}
  };
  panel.onchange=e=>{
    if(e.target.dataset.ovimg!==undefined){const v=e.target.value;if(v){list.push({type:"image",asset:v,x:.82,y:.12,size:.2,t0:0,t1:-1});selI=list.length-1;draw();onchange&&onchange()}return}
  };
  panel.oninput=e=>{
    const k=e.target.dataset.ovp,o=list[selI];if(!k||!o)return;let v=e.target.value;
    if(k==="size")v=(+v)/100;else if(k==="t0")v=Math.max(0,+v||0);else if(k==="t1")v=v===""?-1:Math.max(0,+v);
    o[k]=v;
    const d=stage.querySelector(`.ov[data-k="${selI}"]`);
    if(d){if(o.type==="image")d.style.width=o.size*100+"%";else{d.textContent=o.text;d.style.cssText=`left:${o.x*100}%;top:${o.y*100}%;`+ovCss(o,W())}}
    onchange&&onchange();
  };
  stage.onpointerdown=e=>{const d=e.target.closest(".ov");if(!d)return;selI=+d.dataset.k;const r=stage.getBoundingClientRect(),o=list[selI];
    drag={dx:(e.clientX-r.left)/r.width-o.x,dy:(e.clientY-r.top)/r.height-o.y};stage.setPointerCapture(e.pointerId);
    stage.querySelectorAll(".ov").forEach(x=>x.classList.toggle("sel",+x.dataset.k===selI));drawPanel();e.preventDefault()};
  stage.onpointermove=e=>{if(!drag)return;const r=stage.getBoundingClientRect(),o=list[selI];
    o.x=Math.min(1,Math.max(0,(e.clientX-r.left)/r.width-drag.dx));o.y=Math.min(1,Math.max(0,(e.clientY-r.top)/r.height-drag.dy));
    const d=stage.querySelector(`.ov[data-k="${selI}"]`);if(d){d.style.left=o.x*100+"%";d.style.top=o.y*100+"%"}};
  stage.onpointerup=()=>{if(drag){drag=null;onchange&&onchange()}};
  draw();
  return {redraw:draw};
}
function stageBg(stage,ed){
  const L=effLayout(ed),t=EDT,u=`/api/frame/${JOB.id}/${t}`;
  stage.style.backgroundImage=`url('${u}')`;stage.style.backgroundRepeat="no-repeat";
  if(L==="fill"||L==="auto"){stage.style.backgroundSize=`auto ${ed.zoom*100}%`;stage.style.backgroundPosition=`${ed.cx*100}% ${ed.cy*100}%`}
  else{stage.style.backgroundSize="cover";stage.style.backgroundPosition="50% 50%"}
}
function openEditor(i){
  const c=JOB.clips.find(x=>x.i===i);if(!c)return;const ed=clipEdit(c);
  EDI=i;EDT=Math.round(c.t_peak!=null?c.t_peak:(ed.start+ed.end)/2);EDSHOWVID=false;
  const rank=[...JOB.clips].sort((a,b)=>(b.intensity||0)-(a.intensity||0)).findIndex(x=>x.i===i)+1;
  const m=$("#modal"),b=$("#modalbody");m.classList.remove("hide");m.classList.add("editfs");
  b.innerHTML=`<div class="row"><h2 class="grow" style="margin:0">✏️ Editar clip #${rank} <span class="pill ${esc(c.cat)}">${esc(CATN[c.cat]||c.cat)}</span></h2><button class="btn sm" id="etop">Exportar</button><button class="btn sec sm" id="eclose">Cerrar</button></div>
  ${c.why?`<div class="tiny" style="margin:4px 0">🔥 Nota ${Math.round((c.intensity||0)*10)}/100 · ${esc(c.why)}</div>`:""}
  <div class="big" style="margin-top:10px"><div><div class="stage" id="e_stage"></div>
    <div class="row" style="margin-top:6px;justify-content:center"><button class="btn sec sm" id="e_tv">▶ Ver el clip creado</button></div><div class="tiny" id="e_state" style="text-align:center;margin-top:4px"></div><div class="tiny" style="text-align:center">Vista aproximada: el resultado final puede variar un poco.</div></div>
  <div>
   <div class="tabs" id="e_tabs"><button data-et="fr"><i>🎬</i>Diseño</button><button data-et="ov"><i>🔤</i>Elementos</button><button data-et="ia"><i>✨</i>Mejoras</button><button data-et="au"><i>🎵</i>Audio</button><button data-et="sub"><i>💬</i>Subs</button><button data-et="tm"><i>✂️</i>Recortar</button><button data-et="bg"><i>🖼</i>Fondo</button></div>
   <div id="e_pane"></div>
   <div class="g2" style="margin-top:14px;grid-template-columns:1fr 1fr 1fr"><div><label>Calidad de exportación</label><select id="e_q"><option value="alta" selected>Máxima</option><option value="media">Media</option><option value="baja">Ligera</option></select></div><div><label>Resolución</label><select id="e_res"><option value="1080" selected>1080p</option><option value="720">720p</option></select></div><div><label>Cuadros</label><select id="e_fps"><option value="30" selected>30 fps</option><option value="60">60 fps</option></select></div></div>
   <div class="row" style="margin-top:10px"><button class="btn lg grow" id="e_make">🔄 Rehacer este clip</button></div>
   <div class="row" style="margin-top:8px" id="e_after"></div>
  </div></div>`;
  const E=()=>clipEdit(JOB.clips.find(x=>x.i===i));
  const stage=$("#e_stage");
  let ovm=null;let AUD={};
  const refreshBg=()=>{if(!EDSHOWVID)stageBg(stage,E())};
  const showTab=t=>{
    EDTAB=t;stage.onpointerdown=null;$$("#e_tabs [data-et]").forEach(x=>x.classList.toggle("on",x.dataset.et===t));const e=E(),pane=$("#e_pane");ovm=null;
    if(t==="ov"){pane.innerHTML=`<div id="e_ovp"></div>`;ovm=mountOv(stage,$("#e_ovp"),e.overlays,()=>{})}
    else{stage.querySelectorAll(".ov").forEach(x=>x.remove());stage.onpointerdown=stage.onpointermove=stage.onpointerup=null;
      if(t==="ov")return;
      if(t==="sub")paneSub();
      if(t==="fr")paneFrame();
      if(t==="tm")paneTime();if(t==="bg")paneBg();if(t==="ia")paneIA();if(t==="au")paneAud();
      if(t==="ti")paneTitle();
      /* los textos se siguen viendo (solo lectura) en las otras pestañas */
      e.overlays.forEach(o=>{const d=document.createElement("div");d.className="ov";d.style.left=o.x*100+"%";d.style.top=o.y*100+"%";d.style.pointerEvents="none";d.style.border="0";
        if(o.type==="image"){d.style.width=o.size*100+"%";d.style.padding="0";d.innerHTML=`<img src="/assets/${encodeURIComponent(o.asset)}">`}else{d.textContent=o.text;d.style.cssText+=ovCss(o,stage.clientWidth||300)}stage.appendChild(d)});
    }
    refreshBg();
  };
  function paneTitle(){const e=E();$("#e_pane").innerHTML=`<label>Título del clip</label><input type="text" id="e_title" maxlength="70" value="${esc(e.title)}">
    <div class="row" style="margin:8px 0"><button class="btn sec sm" id="e_ai">✨ Elegir título con IA</button><span class="tiny" id="e_aimsg"></span></div>
    <div class="chk"><input type="checkbox" id="e_ton" ${e.title_on?"checked":""}><span>Mostrar el título arriba (tarjeta blanca)</span></div>`;
    $("#e_title").oninput=ev=>{E().title=ev.target.value};$("#e_ton").onchange=ev=>{E().title_on=ev.target.checked};
    $("#e_ai").onclick=async()=>{const m=$("#e_aimsg"),bt=$("#e_ai");bt.disabled=true;m.textContent="Analizando el video…";
      try{const r=await api("/api/title/"+cur+"/"+i,{json:{}});E().title=r.title;$("#e_title").value=r.title;m.textContent="Listo ✓"}catch(er){m.textContent=er.message}bt.disabled=false}}
  function paneTime(){const e=E();$("#e_pane").innerHTML=`<div class="g2"><div><label>Inicio (m:ss)</label><div class="row"><button class="btn sec sm" data-nudge="start:-1">−1</button><input type="text" id="e_start" value="${fmtT(e.start)}" style="flex:1;min-width:0"><button class="btn sec sm" data-nudge="start:1">+1</button></div></div>
    <div><label>Final (m:ss)</label><div class="row"><button class="btn sec sm" data-nudge="end:-1">−1</button><input type="text" id="e_end" value="${fmtT(e.end)}" style="flex:1;min-width:0"><button class="btn sec sm" data-nudge="end:1">+1</button></div></div></div>
    <div class="tiny" id="e_dur"></div>
    <div id="e_trim" style="position:relative;height:50px;background:var(--card2);border-radius:10px;margin:10px 0;touch-action:none"><div id="e_trsel" style="position:absolute;top:0;bottom:0;background:#38bdf84d;border:2px solid var(--ac);border-radius:8px"></div><div id="e_hs" style="position:absolute;top:-4px;width:26px;height:58px;margin-left:-13px;background:var(--ac);border-radius:8px;touch-action:none"></div><div id="e_he" style="position:absolute;top:-4px;width:26px;height:58px;margin-left:-13px;background:var(--ac);border-radius:8px;touch-action:none"></div></div><div class="tiny">Arrastra los bordes para recortar el inicio y el final.</div>
    <label>Cuadro de referencia: <b id="e_tvv"></b></label><input type="range" id="e_ts" min="${Math.floor(e.start)}" max="${Math.ceil(e.end)}" value="${EDT}">
    <div class="row" style="margin-top:8px"><button class="btn sec sm" id="e_orig">▶ Ver el momento original</button></div><div id="e_origbox" style="margin-top:8px"></div>`;
    const upd=()=>{const e=E();$("#e_dur").textContent=`Dura ${Math.round(e.end-e.start)} s · momento en el directo: ${fmtT(JOB.base_offset+e.start)}`;$("#e_tvv").textContent=fmtT(JOB.base_offset+EDT)};upd();
    const fix=()=>{const e=E(),ts=$("#e_ts");ts.min=Math.floor(e.start);ts.max=Math.ceil(e.end);if(EDT<e.start||EDT>e.end){EDT=Math.round((e.start+e.end)/2);ts.value=EDT}trimmed();upd();refreshBg()};
    const trimmed=()=>{const e=E();if(e.cap_lines.length&&e.cap_for&&(e.cap_for[0]!==e.start||e.cap_for[1]!==e.end)){e.cap_lines=[];e.cap_for=null}};
    ["start","end"].forEach(k=>$("#e_"+k).onchange=ev=>{const v=parseT(ev.target.value),e=E();if(v!==null)e[k]=Math.max(0,Math.min(JOB.meta.duration,v));ev.target.value=fmtT(e[k]);fix()});
    $("#e_pane").onclick=ev=>{const n=ev.target.dataset.nudge;if(n){const [k,d]=n.split(":"),e=E();e[k]=Math.max(0,Math.min(JOB.meta.duration,e[k]+ +d));$("#e_"+k).value=fmtT(e[k]);fix()}};
    const lo=Math.max(0,e.start-30),hi=Math.min(JOB.meta.duration,e.end+30),tr=$("#e_trim");
    const place=()=>{const e=E(),a=(e.start-lo)/(hi-lo)*100,b=(e.end-lo)/(hi-lo)*100;$("#e_trsel").style.cssText+=`;left:${a}%;width:${b-a}%`;$("#e_hs").style.left=a+"%";$("#e_he").style.left=b+"%"};place();
    [["e_hs","start"],["e_he","end"]].forEach(([id,k])=>$("#"+id).onpointerdown=ev=>{ev.preventDefault();const r=tr.getBoundingClientRect();
      const mv=m=>{const e=E();let t=lo+Math.min(1,Math.max(0,(m.clientX-r.left)/r.width))*(hi-lo);t=Math.round(t*2)/2;t=k==="start"?Math.min(t,e.end-3):Math.max(t,e.start+3);e[k]=t;$("#e_"+k).value=fmtT(t);place();upd()};
      const up=()=>{removeEventListener("pointermove",mv);removeEventListener("pointerup",up);fix()};addEventListener("pointermove",mv);addEventListener("pointerup",up)});
    $("#e_ts").onchange=ev=>{EDT=+ev.target.value;upd();refreshBg()};$("#e_ts").oninput=ev=>{$("#e_tvv").textContent=fmtT(JOB.base_offset+ +ev.target.value)};
    $("#e_orig").onclick=()=>{const e=E();$("#e_origbox").innerHTML=`<video controls playsinline autoplay src="/vod/${JOB.id}#t=${e.start},${e.end}" style="width:100%;max-height:300px"></video>`};
  }
  function paneIA(){paneTitle();const S=Object.assign({},JOB.settings||{},AUD);
    $("#e_pane").insertAdjacentHTML("beforeend",`<hr style="border:0;border-top:1px solid var(--line);margin:14px 0"><div class="chk"><input type="checkbox" id="m_zoom" ${S.zoom_peak?"checked":""}><span>Zoom rápido en el momento clave</span></div>
      <div class="chk"><input type="checkbox" id="m_norm" ${S.normalize?"checked":""}><span>Nivelar el volumen</span></div>
      <div class="chk"><input type="checkbox" id="m_cen" ${S.mute_profanity?"checked":""}><span>Tapar groserías</span></div>
      <select id="m_snd"><option value="mute"${S.profanity_sound==="mute"||!S.profanity_sound?" selected":""}>Silencio</option><option value="beep"${S.profanity_sound==="beep"?" selected":""}>Pitido (beep)</option><option value="low"${S.profanity_sound==="low"?" selected":""}>Tono grave</option></select>`);
    $("#e_pane").onchange=ev=>{if(!ev.target.id||ev.target.id.indexOf("m_")!==0)return;AUD.zoom_peak=$("#m_zoom").checked;AUD.normalize=$("#m_norm").checked;AUD.mute_profanity=$("#m_cen").checked;AUD.profanity_sound=$("#m_snd").value}}
  function paneBg(){const e=E(),b=e.bg,ims=ASSETS.filter(a=>a.kind==="logo");
    $("#e_pane").innerHTML=`<div class="chk"><input type="checkbox" id="b_on" ${b.mode==="chroma"?"checked":""}><span>Quitar un color del video (pantalla verde / chroma key)</span></div>
    <div class="g2"><div><label>Color a quitar</label><input type="color" id="b_col" value="#${b.color||"00ff00"}"></div><div><label>Intensidad: <b id="b_sv"></b></label><input type="range" id="b_sim" min="0.05" max="0.5" step="0.01" value="${b.sim||0.25}"></div></div>
    <label>Poner detrás</label><div class="g2"><select id="b_back"><option value="color"${b.back!=="image"?" selected":""}>Un color</option><option value="image"${b.back==="image"?" selected":""}>Una imagen</option></select><input type="color" id="b_bc" value="#${b.bgcolor||"000000"}"></div>
    <select id="b_img"><option value="">Imagen…</option>${ims.map(a=>`<option value="${esc(a.name)}"${b.bgimg===a.name?" selected":""}>${esc(a.name)}</option>`).join("")}</select>
    <div class="tiny">No se ve en la vista previa, solo en el clip final. Borrar fondo con IA aún no está disponible.</div>`;
    const set=()=>{b.mode=$("#b_on").checked?"chroma":"none";b.color=$("#b_col").value.slice(1);b.sim=+$("#b_sim").value;b.back=$("#b_back").value;b.bgcolor=$("#b_bc").value.slice(1);b.bgimg=$("#b_img").value;$("#b_sv").textContent=b.sim.toFixed(2)};
    $("#e_pane").oninput=$("#e_pane").onchange=set;set()}
  function paneAud(){const ms=ASSETS.filter(a=>a.kind==="music"),S=JOB.settings||{},m0=AUD.music!==undefined?AUD.music:S.music;
    $("#e_pane").innerHTML=`<label>Música de fondo</label><select id="a_m"><option value="">Ninguna</option>${ms.map(a=>`<option value="${esc(a.name)}"${m0===a.name?" selected":""}>${esc(a.name)}</option>`).join("")}</select>
    <label>Volumen: <b id="a_vv"></b></label><input type="range" id="a_v" min="0.03" max="0.6" step="0.01" value="${AUD.music_volume!==undefined?AUD.music_volume:(S.music_volume||0.18)}">
    <div class="tiny">${ms.length?"La música baja sola cuando hablan.":"Sube tu música en Mi cuenta → Música, logo e imágenes."}</div>`;
    const set=()=>{AUD.music=$("#a_m").value;AUD.music_volume=+$("#a_v").value;$("#a_vv").textContent=AUD.music_volume.toFixed(2)};
    $("#e_pane").oninput=$("#e_pane").onchange=set;set()}
  function paneFrame(){var pkPlace=null;const e=E(),L=effLayout(e);$("#e_pane").innerHTML=`<label>Diseño de este clip</label>
    <div class="lgrid" id="e_lay">${Object.entries(LAYB).map(([k,t])=>`<button class="lc" data-l="${k}">${layMini(k)}<span style="pointer-events:none">${esc(t)}</span></button>`).join("")}</div>
    <div id="e_splitbox" style="margin-top:12px"><label>Altura de la cámara: <b id="sp_v"></b>%</label><input type="range" id="sp" min="20" max="60" value="${AUD.split_pct!==undefined?AUD.split_pct:((JOB.settings&&JOB.settings.split_pct)||38)}">
      <div class="seg" id="co" style="margin-top:6px"><button data-co="top">Cámara arriba</button><button data-co="bottom">Cámara abajo</button></div>
      <div class="row" style="margin-top:8px"><button class="btn sec sm" id="lay_all">Aplicar a todos los clips</button><span class="tiny" id="lay_msg"></span></div></div>
    <div id="e_camwarn"></div>
    <div id="e_crop"><h3>Encuadre (pantalla completa)</h3><div class="tiny">Mueve la zona y el zoom hasta que se vea lo que quieres (tu cámara, la pantalla…). Se aplica con “Pantalla completa” (o “Inteligente” si elige ese diseño).</div>
      <label>Izquierda ↔ Derecha: <b id="e_xv"></b>%</label><input type="range" id="e_cx" min="0" max="100" value="${Math.round(e.cx*100)}">
      <label>Arriba ↔ Abajo: <b id="e_yv"></b>%</label><input type="range" id="e_cy" min="0" max="100" value="${Math.round(e.cy*100)}">
      <label>Zoom: <b id="e_zv"></b>×</label><input type="range" id="e_zoom" min="1" max="4" step="0.05" value="${e.zoom}">
      <div class="seg" style="margin-top:6px"><button data-pos="0.5,0.5">Centro</button><button data-pos="0,0.5">Izquierda</button><button data-pos="1,0.5">Derecha</button><button data-pos="0.5,0">Arriba</button><button data-pos="0.5,1">Abajo</button></div></div>`;
    const upd=()=>{const e=E(),L=effLayout(e);if(pkPlace)pkPlace();$$("#e_lay [data-l]").forEach(bt=>bt.classList.toggle("on",bt.dataset.l===(e.layout||"")));
      $("#e_xv").textContent=Math.round(e.cx*100);$("#e_yv").textContent=Math.round(e.cy*100);$("#e_zv").textContent=(+e.zoom).toFixed(2);
      $("#e_crop").classList.toggle("hide",!(L==="fill"||L==="auto"));
      $("#e_camwarn").innerHTML=(camBig(JOB)&&(L==="split"||L==="circle"||L==="cam"))?`<div class="msg warn">Tu cuadro de cámara ocupa casi todo el video, por eso este diseño se ve raro. Prueba “Pantalla completa vertical”.</div>`:"";refreshBg()};
    $("#e_pane").onclick=ev=>{const l=ev.target.dataset.l;if(l!==undefined&&ev.target.closest("#e_lay")){E().layout=l;upd()}
      const p=ev.target.dataset.pos;if(p){const [x,y]=p.split(",").map(Number),e=E();e.cx=x;e.cy=y;$("#e_cx").value=x*100;$("#e_cy").value=y*100;upd()}};
    $("#e_pane").oninput=ev=>{const e=E();if(ev.target.id==="e_cx")e.cx=ev.target.value/100;if(ev.target.id==="e_cy")e.cy=ev.target.value/100;if(ev.target.id==="e_zoom")e.zoom=+ev.target.value;upd()};
const crop=$("#e_crop");crop.querySelectorAll("label,input[type=range]").forEach(x=>x.style.display="none");
    const pk=document.createElement("div");pk.style.cssText="position:relative;width:100%;touch-action:none;margin:8px 0;background:#000;border-radius:10px;overflow:hidden";
    pk.innerHTML=`<img id="pk_img" src="/api/frame/${JOB.id}/${EDT}" style="display:block;width:100%" draggable="false"><div id="pk_r" style="position:absolute;border:3px solid var(--ac);box-shadow:0 0 0 999px #000a;box-sizing:border-box;touch-action:none"><div id="pk_h" style="position:absolute;right:-16px;bottom:-16px;width:32px;height:32px;border-radius:50%;background:var(--ac);touch-action:none"></div></div>`;
    crop.querySelector(".tiny").after(pk);crop.querySelector(".tiny").textContent="Arrastra el recuadro para elegir qué se ve. Usa el círculo de la esquina para hacerlo más grande o pequeño (zoom).";
    const oa=9/16,pimg=pk.querySelector("img"),pr=pk.querySelector("#pk_r");
    const geo=()=>{const ar=(pimg.naturalWidth||16)/(pimg.naturalHeight||9),e=E(),zmin=Math.max(1,oa/ar),z=Math.min(4,Math.max(e.zoom,zmin));return {ar,zmin,z,hf:1/z,wf:Math.min(1,oa/ar/z)}};
    pkPlace=()=>{const e=E(),g=geo();pr.style.width=g.wf*100+"%";pr.style.height=g.hf*100+"%";pr.style.left=e.cx*(1-g.wf)*100+"%";pr.style.top=e.cy*(1-g.hf)*100+"%"};
    pimg.onload=pkPlace;pkPlace();
    pr.onpointerdown=ev=>{if(ev.target.id==="pk_h")return;ev.preventDefault();const b=pk.getBoundingClientRect(),e=E(),g=geo();let l=e.cx*(1-g.wf),t=e.cy*(1-g.hf),x0=ev.clientX,y0=ev.clientY;
      const mv=m=>{l=Math.min(1-g.wf,Math.max(0,l+(m.clientX-x0)/b.width));t=Math.min(1-g.hf,Math.max(0,t+(m.clientY-y0)/b.height));x0=m.clientX;y0=m.clientY;e.cx=1-g.wf>0.001?l/(1-g.wf):0.5;e.cy=1-g.hf>0.001?t/(1-g.hf):0.5;upd()};
      const up=()=>{removeEventListener("pointermove",mv);removeEventListener("pointerup",up)};addEventListener("pointermove",mv);addEventListener("pointerup",up)};
    pk.querySelector("#pk_h").onpointerdown=ev=>{ev.preventDefault();ev.stopPropagation();const b=pk.getBoundingClientRect(),e=E();
      const mv=m=>{const g=geo(),w=Math.max(0.05,(m.clientX-b.left)/b.width-e.cx*(1-g.wf));e.zoom=Math.min(4,Math.max(g.zmin,oa/g.ar/Math.min(1,w)));upd()};
      const up=()=>{removeEventListener("pointermove",mv);removeEventListener("pointerup",up)};addEventListener("pointermove",mv);addEventListener("pointerup",up)};
const sp=$("#sp"),spv=()=>{$("#sp_v").textContent=sp.value;$$("#co [data-co]").forEach(b=>b.classList.toggle("on",b.dataset.co===(AUD.cam_order||(JOB.settings&&JOB.settings.cam_order)||"top")))};
    sp.oninput=()=>{AUD.split_pct=+sp.value;spv()};spv();
    $$("#co [data-co]").forEach(b=>b.onclick=()=>{AUD.cam_order=b.dataset.co;spv()});
    $("#lay_all").onclick=async()=>{const l=E().layout;JOB.clips.forEach(c=>{clipEdit(c).layout=l});AUD.split_pct=+sp.value;AUD.cam_order=AUD.cam_order||"top";
      try{await api("/api/settings/"+cur,{json:Object.assign({split_pct:+sp.value,cam_order:AUD.cam_order},l?{layout:l}:{})});$("#lay_msg").textContent=" Aplicado a todos ✓"}catch(er){$("#lay_msg").textContent=er.message}};
    stage.onpointerdown=ev=>{if(ev.target.closest(".ov"))return;const e=E(),r=stage.getBoundingClientRect();let x0=ev.clientX,y0=ev.clientY;
      const mv=m=>{const k=1.3/(e.zoom||1);e.cx=Math.min(1,Math.max(0,e.cx-(m.clientX-x0)/r.width*k));e.cy=Math.min(1,Math.max(0,e.cy-(m.clientY-y0)/r.height*k));x0=m.clientX;y0=m.clientY;$("#e_cx").value=e.cx*100;$("#e_cy").value=e.cy*100;upd()};
      const up=()=>{removeEventListener("pointermove",mv);removeEventListener("pointerup",up)};addEventListener("pointermove",mv);addEventListener("pointerup",up)};
    upd();
  }
  function paneSub(){const e=E();
    $("#e_pane").innerHTML=`<div class="sub">Corrige las palabras que la IA escuchó mal. Se usan al rehacer el clip.</div>
      <div class="row" style="margin-top:8px"><button class="btn sm" id="e_loadsub">${e.cap_lines.length?"Volver a cargar":"Cargar subtítulos del clip"}</button>${e.cap_lines.length?'<button class="btn sec sm" id="e_clrsub">Quitar mis cambios</button>':""}</div>
      <div id="e_submsg"></div><div id="e_sublines">${e.cap_lines.map((l,k)=>`<div class="row" style="margin:5px 0"><span class="tiny" style="width:42px">${(+l[0]).toFixed(1)}s</span><input type="text" data-sl="${k}" value="${esc(l[2])}" maxlength="90" style="flex:1;min-width:0"></div>`).join("")}</div>
      ${(JOB.settings&&JOB.settings.captions)?"":'<div class="msg warn">Los subtítulos están apagados en “Diseño y ajustes”; enciéndelos para que se vean.</div>'}`;
    $("#e_loadsub").onclick=async()=>{const e=E();$("#e_submsg").innerHTML='<div class="sub">Escuchando el clip…</div>';
      try{const r=await api("/api/captions/"+cur,{json:{start:e.start,end:e.end}});e.cap_lines=r.lines;e.cap_for=[e.start,e.end];paneSub()}catch(er){$("#e_submsg").innerHTML=`<div class="msg bad">${esc(er.message)}</div>`}};
    const cl=$("#e_clrsub");if(cl)cl.onclick=()=>{E().cap_lines=[];E().cap_for=null;paneSub()};
    $("#e_pane").oninput=ev=>{const k=ev.target.dataset.sl;if(k!==undefined)E().cap_lines[+k][2]=ev.target.value};
  }
  $("#e_tabs").onclick=ev=>{const t=ev.target.dataset.et;if(t){EDSHOWVID=false;restoreStage();showTab(t)}};
  function restoreStage(){const v=stage.querySelector("video");if(v)v.remove();$("#e_tv").textContent="▶ Ver el clip creado"}
  $("#e_tv").onclick=()=>{const last=exportsOf(i)[0];
    if(EDSHOWVID){EDSHOWVID=false;restoreStage();showTab(EDTAB);return}
    if(!last||last.status!=="done"){alert("Este clip todavía no está creado.");return}
    EDSHOWVID=true;stage.innerHTML="";stage.style.backgroundImage="none";const v=document.createElement("video");v.controls=true;v.playsInline=true;v.autoplay=true;v.src=`/clipfile/${JOB.id}/${last.n}`;v.style.cssText="width:100%;height:100%;object-fit:cover;max-height:none;border-radius:0";stage.appendChild(v);$("#e_tv").textContent="✏️ Volver a editar"};
  $("#eclose").onclick=()=>{m.classList.add("hide");EDI=null;stage.innerHTML=""};
  $("#etop").onclick=()=>$("#e_make").click();
  $("#e_make").onclick=async()=>{const e=E();if(e.end-e.start<3){alert("El clip debe durar al menos 3 segundos");return}
    $("#e_make").disabled=true;await makeClips([i],Object.assign($("#set-job").getSettings(),AUD,{quality:$("#e_q").value,resolution:$("#e_res").value,fps:$("#e_fps").value}));await poll(true);$("#e_make").disabled=false;EDSHOWVID=false;restoreStage();showTab(EDTAB)};
  if(!LAYASKED[JOB.id]){LAYASKED[JOB.id]=1;EDTAB="fr"}
  showTab(EDTAB);syncEditor();
}
function syncEditor(){
  const i=EDI,last=exportsOf(i)[0],st=$("#e_state"),af=$("#e_after");if(!st)return;
  const done=last&&last.status==="done",busy=last&&(last.status==="queued"||last.status==="running");
  st.textContent=busy?`${last.stage||"Creando…"} ${last.progress}%${etaTxt(last.eta)}`:(last&&last.status==="error"?"Error: "+(last.error||""):(done?"Clip listo ✓":"Todavía no se creó este clip"));
  const key=done?"d"+last.n:"x";
  if(af.dataset.k!==key){af.dataset.k=key;
    af.innerHTML=done?`<a class="btn sec" href="/clipfile/${JOB.id}/${last.n}?dl=1" style="text-decoration:none">⬇️ Descargar</a><button class="btn sec" id="e_share">Compartir</button><button class="btn ok" id="e_pub">Publicar / programar</button>`:"";
    if(done){$("#e_share").onclick=()=>shareClip(last);$("#e_pub").onclick=()=>{$("#modal").classList.add("hide");EDI=null;openPublish([i])}}}
}
/* --- textos e imagenes de TODOS los clips --- */
$("#gov").onclick=()=>{
  const el=$("#set-job"),m=$("#modal"),b=$("#modalbody");m.classList.remove("hide");EDI=null;
  const c=JOB.clips[0],t=c?Math.round(c.t_peak||c.start):0;
  b.innerHTML=`<div class="row"><h2 class="grow" style="margin:0">🖼️ Textos e imágenes de todos los clips</h2><button class="btn sm" id="gclose">Listo</button></div>
   <div class="sub">Salen en todos los clips (por ejemplo “Kick TuNombre” o tu logo). Para que se apliquen pulsa después “Guardar y rehacer todos”.</div>
   <div class="big" style="margin-top:10px"><div><div class="stage" id="g_stage" style="background-image:url('/api/frame/${JOB.id}/${t}');background-size:cover"></div></div><div id="g_panel"></div></div>`;
  mountOv($("#g_stage"),$("#g_panel"),el._ov,()=>{});
  $("#gclose").onclick=()=>m.classList.add("hide");
};
/* --- filtros y orden --- */
const CATGRP=c=>["risas","terror","polemica","epico","fail"].includes(c)?c:"otro";
$(".tools").addEventListener("click",e=>{const f=e.target.dataset.f;if(f){FILT=f;$$(".tools .fchip").forEach(x=>x.classList.toggle("on",x.dataset.f===f));if(JOB)renderClips()}});
$("#sortsel").onchange=e=>{SORT=e.target.value;if(JOB)renderClips()};
/* --- calendario --- */
let CALM=new Date();CALM.setDate(1);
async function loadCal(){
  let q=[];try{q=await api("/api/queue")}catch(e){}
  const y=CALM.getFullYear(),mo=CALM.getMonth();
  $("#calttl").textContent=CALM.toLocaleDateString("es",{month:"long",year:"numeric"});
  const first=new Date(y,mo,1),start=(first.getDay()+6)%7,days=new Date(y,mo+1,0).getDate(),today=new Date();
  const by={};q.forEach(t=>{const d=new Date((t.when||t.created)*1000);if(d.getFullYear()===y&&d.getMonth()===mo){(by[d.getDate()]=by[d.getDate()]||[]).push(t)}});
  let h=["L","M","X","J","V","S","D"].map(x=>`<div class="dn">${x}</div>`).join("");
  for(let k=0;k<start;k++)h+='<div class="day out"></div>';
  for(let d=1;d<=days;d++){const ev=by[d]||[];const isT=today.getFullYear()===y&&today.getMonth()===mo&&today.getDate()===d;
    h+=`<div class="day${isT?" today":""}" data-d="${d}"><b>${d}</b>${ev.slice(0,3).map(t=>`<div class="ev ${esc(t.platform)}">${t.platform==="facebook"?"FB":"TT"} ${esc((t.title||"Clip").slice(0,14))}</div>`).join("")}${ev.length>3?`<div class="tiny">+${ev.length-3}</div>`:""}</div>`}
  $("#calgrid").innerHTML=h;
  $("#calgrid").onclick=e=>{const dd=e.target.closest("[data-d]");if(!dd)return;const ev=by[+dd.dataset.d]||[];
    $("#calday").innerHTML=`<h3 style="margin-top:0">${dd.dataset.d} de ${CALM.toLocaleDateString("es",{month:"long"})}</h3>`+(ev.length?ev.map(t=>`<div class="q" style="margin:6px 0"><div><b>${t.platform==="facebook"?"Facebook":"TikTok"}</b> · ${esc(t.title||"Clip")}<div class="tiny">${esc(t.when_txt)} · ${esc(QST[t.status]?QST[t.status][0]:t.status)}</div></div></div>`).join(""):'<div class="sub">Nada programado este día.</div>')};
}
$("#calprev").onclick=()=>{CALM.setMonth(CALM.getMonth()-1);loadCal()};
$("#calnext").onclick=()=>{CALM.setMonth(CALM.getMonth()+1);loadCal()};
/* --- analiticas --- */
async function loadAna(){
  try{const h=await api("/api/home");$("#a_found").textContent=h.found;$("#a_avg").textContent=h.avg;$("#a_fb").textContent=h.fb;$("#a_tt").textContent=h.tt;
    const mx=Math.max(1,...Object.values(h.cats||{}));
    $("#a_cats").innerHTML=Object.entries(h.cats||{}).sort((a,b)=>b[1]-a[1]).map(([k,v])=>`<div class="row" style="margin:6px 0"><span style="width:110px">${esc(CATN[k]||k)}</span><div class="bar grow" style="margin:0"><i style="width:${100*v/mx}%"></i></div><b>${v}</b></div>`).join("")||'<div class="sub">Todavía no hay datos.</div>'}catch(e){}
}
/* --- agente IA / video de referencia --- */
let AGRES=null;
$("#ag_go").onclick=async()=>{
  const f=$("#ag_file").files[0],name=$("#ag_name").value.trim(),prompt=$("#ag_prompt").value.trim();
  if(!f&&!prompt){$("#ag_msg").innerHTML='<div class="msg bad">Sube un video de referencia o escribe lo que quieres.</div>';return}
  $("#ag_msg").innerHTML='<div class="sub">Analizando… (puede tardar un poco)</div>';$("#ag_go").disabled=true;
  try{let r;
    if(f){const fd=new FormData();fd.append("file",f);fd.append("name",name);fd.append("prompt",prompt);r=await api("/api/reference",{method:"POST",body:fd})}
    else r=await api("/api/agent",{json:{name,prompt}});
    AGRES=r;$("#ag_msg").innerHTML="";showAgent(r)}
  catch(e){$("#ag_msg").innerHTML=`<div class="msg bad">${esc(e.message)}</div>`}
  $("#ag_go").disabled=false;
};
function showAgent(r){
  const st=r.settings||{},ov=r.overlays||[];
  const L={fill:"Pantalla completa",split:"Cámara + gameplay",circle:"Cámara en círculo",dual:"Dos pantallas"};
  $("#ag_res").classList.remove("hide");
  $("#ag_res").innerHTML=`<h2>Estilo encontrado</h2><div class="sub">${esc(r.notes||"")}</div>
   <div style="margin:8px 0">${st.layout?`<span class="chipx">Diseño: ${esc(L[st.layout]||st.layout)}</span>`:""}${st.titles!==undefined?`<span class="chipx">Título: ${st.titles?"sí":"no"}</span>`:""}${st.captions!==undefined?`<span class="chipx">Subtítulos: ${st.captions?"sí":"no"}</span>`:""}${st.caption_style?`<span class="chipx">Estilo: ${esc(st.caption_style)}</span>`:""}${st.logo_pos?`<span class="chipx">Logo: ${esc(st.logo_pos)}</span>`:""}
   ${ov.map(o=>`<span class="chipx">🔤 ${esc(o.text)}</span>`).join("")}</div>
   <div class="row"><button class="btn" id="ag_def">Usar como estilo por defecto</button>${cur&&JOB&&JOB.status==="ready"?'<button class="btn ok" id="ag_apply">Aplicar al stream abierto y rehacer</button>':""}<button class="btn sec" id="ag_tpl">Guardar como plantilla</button></div><div id="ag_m2"></div>`;
  const merged=base=>Object.assign({},base,st,{overlays:ov});
  $("#ag_def").onclick=async()=>{try{CFG=await api("/api/config",{json:{defaults:merged(CFG.defaults)}});$("#ag_m2").innerHTML='<div class="msg ok">Listo: los próximos streams usan este estilo.</div>'}catch(e){$("#ag_m2").innerHTML=`<div class="msg bad">${esc(e.message)}</div>`}};
  const ap=$("#ag_apply");if(ap)ap.onclick=async()=>{try{const s2=merged(JOB.settings);await api("/api/settings/"+cur,{json:s2});await makeClips(JOB.clips.map(c=>c.i),s2);$("#ag_m2").innerHTML='<div class="msg ok">Rehaciendo los clips con ese estilo. Míralos en Clips.</div>';renderSettings($("#set-job"),s2)}catch(e){$("#ag_m2").innerHTML=`<div class="msg bad">${esc(e.message)}</div>`}};
  $("#ag_tpl").onclick=async()=>{const n=prompt("Nombre de la plantilla:");if(!n)return;try{await api("/api/templates",{json:{name:n,settings:merged(CFG.defaults)}});$("#ag_m2").innerHTML='<div class="msg ok">Plantilla guardada.</div>'}catch(e){$("#ag_m2").innerHTML=`<div class="msg bad">${esc(e.message)}</div>`}};
}

/* ---------- Publicar / programar ---------- */
async function openPublish(ids){
  EDI=null;await loadAcc(); const A=ACC, j=JOB;
  const items=ids.map(i=>({i,ex:exportsOf(i).find(e=>e.status==="done"),c:j.clips.find(c=>c.i===i)})).filter(x=>x.ex);
  const m=$("#modal"),b=$("#modalbody");m.classList.remove("hide");
  const d=new Date(Date.now()+3600e3);d.setMinutes(0,0,0);const dv=new Date(d-d.getTimezoneOffset()*60000).toISOString().slice(0,16);
  b.innerHTML=`<div class="row"><h2 class="grow" style="margin:0">Publicar ${items.length} clip${items.length>1?"s":""}</h2><button class="btn sec sm" id="mclose">Cerrar</button></div>
  <h3>¿Dónde?</h3>
  <label class="chk"><input type="checkbox" id="p_fb" ${A.facebook.connected?"checked":"disabled"}><span>Facebook Reels ${A.facebook.connected?"· "+esc(A.facebook.page_name):"· <a href='#acc' id='gocuentas'>conectar</a>"}</span></label>
  <label class="chk"><input type="checkbox" id="p_tt" ${A.tiktok.connected?"checked":"disabled"}><span>TikTok ${A.tiktok.connected?"· "+esc(A.tiktok.name):"· <a href='#acc' id='gocuentas2'>conectar</a>"}</span></label>
  <div id="ttopts" class="hide"><div class="g2"><div><label>TikTok: modo</label><select id="tt_mode"><option value="direct">Publicar directo</option><option value="draft">Enviar a borradores</option></select></div>
  <div><label>TikTok: quién lo ve</label><select id="tt_priv"><option value="SELF_ONLY">Solo yo (privado)</option><option value="PUBLIC_TO_EVERYONE">Público</option><option value="MUTUAL_FOLLOW_FRIENDS">Amigos</option><option value="FOLLOWER_OF_CREATOR">Seguidores</option></select></div></div>
  <div class="tiny">Si tu app de TikTok aún no fue auditada, TikTok solo permite privado.</div></div>
  <h3>¿Cuándo?</h3>
  <select id="when"><option value="now">Ahora mismo</option><option value="at">Programar fecha y hora</option></select>
  <div id="whenbox" class="hide"><label>Fecha y hora (tu hora local)</label><input type="datetime-local" id="whendt" value="${dv}">
  ${items.length>1?`<label>Separar cada clip por (horas)</label><input type="number" id="gap" value="3" min="0" max="72" step="0.5"><div class="tiny">El primero sale a esa hora y los demás van espaciados.</div>`:""}</div>
  <h3>Textos y hashtags</h3><div class="row"><button class="btn sec sm" id="suggest">✨ Sugerir textos</button><span class="tiny" id="sugmsg"></span></div>
  <div id="pitems">${items.map(x=>`<div class="card" data-i="${x.i}" data-n="${x.ex.n}"><b>${esc(x.ex.title||"Clip "+(x.i+1))}</b>
    <label>Texto</label><textarea data-cap maxlength="2000">${esc(x.ex.title||"")}</textarea>
    <label>Hashtags (separados por espacio)</label><input type="text" data-tags value="#kick #streamer #fyp"></div>`).join("")}</div>
  <div id="pmsg"></div><div class="row"><button class="btn grow ok" id="psend">Enviar</button></div>`;
  const upd=()=>{$("#ttopts").classList.toggle("hide",!$("#p_tt").checked);$("#whenbox").classList.toggle("hide",$("#when").value!=="at")};
  b.onchange=upd;upd();
  $("#mclose").onclick=()=>m.classList.add("hide");
  ["gocuentas","gocuentas2"].forEach(id=>{const a=$("#"+id);if(a)a.onclick=ev=>{ev.preventDefault();m.classList.add("hide");tab("acc")}});
  $("#suggest").onclick=async()=>{$("#sugmsg").textContent="Pensando…";try{const r=await api("/api/suggest/"+cur,{json:{ids:items.map(x=>x.i)}});
    r.forEach(s=>{const el=$(`#pitems [data-i="${s.i}"]`);if(!el)return;el.querySelector("[data-cap]").value=s.caption;el.querySelector("[data-tags]").value=s.hashtags.map(h=>"#"+h.replace(/^#/,"")).join(" ")});$("#sugmsg").textContent=CFG.ai?"Listo ✓":"Listo (sin IA son textos básicos)"}catch(e){$("#sugmsg").textContent=e.message}};
  $("#psend").onclick=async()=>{
    const plats=[];if($("#p_fb").checked)plats.push("facebook");if($("#p_tt").checked)plats.push("tiktok");
    if(!plats.length){$("#pmsg").innerHTML='<div class="msg bad">Elige al menos una red.</div>';return}
    let t0=null;if($("#when").value==="at"){t0=new Date($("#whendt").value).getTime()/1000;if(!t0||t0<Date.now()/1000+30){$("#pmsg").innerHTML='<div class="msg bad">Elige una fecha futura.</div>';return}}
    const gap=(+($("#gap")?.value||0))*3600;const specs=[];
    $$("#pitems [data-i]").forEach((el,k)=>{const tags=el.querySelector("[data-tags]").value.split(/\s+/).map(s=>s.replace(/^#/,"")).filter(Boolean);
      plats.forEach(p=>specs.push({job:cur,export:+el.dataset.n,platform:p,caption:el.querySelector("[data-cap]").value,hashtags:tags,when:t0?t0+k*gap:null,
        privacy:$("#tt_priv").value,tt_mode:$("#tt_mode").value}))});
    $("#psend").disabled=true;
    try{const r=await api("/api/publish",{json:{items:specs}});
      if(r.errors.length&&!r.created){$("#pmsg").innerHTML=`<div class="msg bad">${r.errors.map(x=>esc(x.error)).join("<br>")}</div>`;$("#psend").disabled=false;return}
      m.classList.add("hide");tab("cola");if(r.errors.length)alert(r.errors.map(x=>x.error).join("\n"))}
    catch(e){$("#pmsg").innerHTML=`<div class="msg bad">${esc(e.message)}</div>`;$("#psend").disabled=false}
  };
}

/* ---------- Cola ---------- */
const QST={pending:["En espera","warn"],running:["Enviando…","warn"],done:["Listo","ok"],error:["Error","err"],cancelled:["Cancelado",""]};
async function refreshBadge(){try{const q=await api("/api/queue");const n=q.filter(t=>t.status==="pending"||t.status==="running").length;$("#qb").textContent=n;$("#qb").classList.toggle("hide",!n)}catch(e){}}
async function loadQueue(){
  try{const q=await api("/api/queue");const n=q.filter(t=>t.status==="pending"||t.status==="running").length;$("#qb").textContent=n;$("#qb").classList.toggle("hide",!n);
    $("#queue").innerHTML=q.length?q.map(t=>{const [lab,cl]=QST[t.status]||[t.status,""];
      const res=t.result?`<div class="tiny">${esc(t.result.note||"")} ${t.result.url?`· <a href="${esc(t.result.url)}" target="_blank" rel="noopener">abrir</a>`:""}</div>`:"";
      return `<div class="card"><div class="q"><div><b>${t.platform==="facebook"?"Facebook":"TikTok"}</b> · ${esc(t.title||"Clip")}
      <div class="tiny">${t.native&&t.status==="pending"?"Se sube ya y Facebook lo publica el "+esc(t.when_txt):esc(t.when_txt)}${t.stage&&t.status!=="done"?" · "+esc(t.stage):""}</div></div><span class="pill ${cl}">${lab}</span></div>
      ${t.caption?`<div class="tiny" style="margin-top:6px">${esc(t.caption.slice(0,100))}</div>`:""}${res}${t.error?`<div class="msg bad">${esc(t.error)}</div>`:""}
      <div class="row" style="margin-top:8px">${t.status==="pending"?`<button class="btn bad sm" data-qa="cancel" data-id="${t.id}">Cancelar</button>`:""}
      ${t.status==="error"||t.status==="cancelled"?`<button class="btn sec sm" data-qa="retry" data-id="${t.id}">Reintentar ahora</button>`:""}
      ${t.status!=="pending"&&t.status!=="running"?`<button class="btn sec sm" data-qa="del" data-id="${t.id}">Quitar</button>`:""}</div></div>`}).join(""):'<div class="card sub">No hay publicaciones todavía. Abre un clip y toca “Publicar / programar”.</div>'}catch(e){}
}
$("#queue").onclick=async e=>{const b=e.target.closest("[data-qa]");if(!b)return;const id=b.dataset.id,a=b.dataset.qa;
  try{if(a==="cancel")await api(`/api/queue/${id}/cancel`,{method:"POST"});if(a==="retry")await api(`/api/queue/${id}/retry`,{method:"POST"});if(a==="del")await api(`/api/queue/${id}`,{method:"DELETE"})}catch(er){alert(er.message)}loadQueue()};

/* ---------- Cuentas ---------- */
async function loadAcc(){ACC=await api("/api/accounts");renderAcc();return ACC}
function renderAcc(){
  const f=ACC.facebook,t=ACC.tiktok;
  $("#acc-fb").innerHTML=`<div class="row"><h2 class="grow" style="margin:0">Facebook (Reels de tu página)</h2><span class="pill ${f.connected?"ok":""}">${f.connected?"Conectado: "+esc(f.page_name):"Sin conectar"}</span></div>
  <div class="sub">Facebook publica Reels solo en <b>páginas</b>, no en perfiles personales.</div>
  <details><summary>Cómo conectar (una vez)</summary><ol class="sub">
   <li>Entra a <b>developers.facebook.com</b> → Mis apps → Crear app (tipo “Empresa”).</li>
   <li>Copia el <b>ID de la app</b> y la <b>clave secreta</b> (Configuración → Básica) y pégalos abajo.</li>
   <li>En “Inicio de sesión con Facebook → Configuración” agrega esta URI de redirección: <code>${esc(f.redirect)}</code></li>
   <li>Pulsa “Conectar con Facebook” y elige tu página. (La app puede quedarse en modo desarrollo si tú eres administrador.)</li></ol>
   <div class="sub">Alternativa rápida: pega el <b>ID de tu página</b> y un <b>token de página</b> (Explorador de la API de Graph).</div></details>
  <label>ID de la app</label><input type="text" id="fb_id" value="${esc(f.app_id)}" autocomplete="off">
  <label>Clave secreta ${f.has_secret?"(guardada ✓)":""}</label><input type="password" id="fb_sec" placeholder="${f.has_secret?"•••••• (déjalo vacío para conservarla)":""}" autocomplete="off">
  <div class="row" style="margin-top:10px"><button class="btn sec" id="fb_save">Guardar datos</button><button class="btn" id="fb_login">Conectar con Facebook</button>${f.connected?'<button class="btn bad" id="fb_disc">Desconectar</button>':""}</div>
  ${f.pages.length>1?`<label>Página a usar</label><select id="fb_page">${f.pages.map(p=>`<option value="${esc(p.id)}"${p.id===f.page_id?" selected":""}>${esc(p.name)}</option>`).join("")}</select>`:""}
  <details><summary>Usar ID de página + token</summary><label>ID de la página</label><input type="text" id="fb_pid"><label>Token de la página</label><input type="password" id="fb_tok"><div class="row" style="margin-top:8px"><button class="btn sec" id="fb_man">Conectar así</button></div></details><div id="fbmsg"></div>`;
  $("#acc-tt").innerHTML=`<div class="row"><h2 class="grow" style="margin:0">TikTok</h2><span class="pill ${t.connected?"ok":""}">${t.connected?"Conectado: "+esc(t.name):"Sin conectar"}</span></div>
  <div class="msg warn">TikTok exige una app de desarrollador. Mientras TikTok no la <b>audite</b>, todo lo que subas queda <b>privado</b> (solo tú). Para publicar en público hay que pasar su auditoría. Con “Enviar a borradores” puedes terminar de publicar desde la app de TikTok.</div>
  <details><summary>Cómo conectar (una vez)</summary><ol class="sub">
   <li>Entra a <b>developers.tiktok.com</b> → Manage apps → Connect an app. Agrega el producto <b>Login Kit</b> y <b>Content Posting API</b> (marca “Direct Post”).</li>
   <li>Copia <b>Client key</b> y <b>Client secret</b>.</li>
   <li>TikTok no acepta http://localhost. Usa una dirección <b>https</b> que tú controles como Redirect URI (por ejemplo <code>https://example.com/callback</code>; no tiene que existir). Debe ser igual aquí y en TikTok.</li>
   <li>Pulsa “Conectar TikTok”, autoriza, y cuando el navegador te lleve a esa página (aunque diga error), <b>copia la dirección completa</b> de la barra y pégala abajo.</li></ol></details>
  <label>Client key</label><input type="text" id="tt_key" value="${esc(t.client_key)}" autocomplete="off">
  <label>Client secret ${t.has_secret?"(guardado ✓)":""}</label><input type="password" id="tt_sec" placeholder="${t.has_secret?"•••••• (déjalo vacío para conservarlo)":""}" autocomplete="off">
  <label>Redirect URI (https)</label><input type="text" id="tt_red" value="${esc(t.redirect_uri)}" placeholder="https://example.com/callback" autocomplete="off">
  <div class="row" style="margin-top:10px"><button class="btn sec" id="tt_save">Guardar datos</button><button class="btn" id="tt_login">Conectar TikTok</button>${t.connected?'<button class="btn bad" id="tt_disc">Desconectar</button>':""}</div>
  <label>Pega aquí la dirección a la que te llevó TikTok</label><input type="text" id="tt_paste" placeholder="https://example.com/callback?code=…" autocomplete="off">
  <div class="row" style="margin-top:8px"><button class="btn ok" id="tt_fin">Terminar conexión</button></div><div id="ttmsg"></div>`;
  const msg=(id,c,t)=>$("#"+id).innerHTML=`<div class="msg ${c}">${esc(t)}</div>`;
  const act=(id,fn,mid)=>{const b=$("#"+id);if(b)b.onclick=async()=>{try{await fn();}catch(e){msg(mid,"bad",e.message)}}};
  act("fb_save",async()=>{ACC=await api("/api/fb/app",{json:{app_id:$("#fb_id").value,app_secret:$("#fb_sec").value}});renderAcc();msg("fbmsg","ok","Guardado")},"fbmsg");
  act("fb_login",async()=>{await api("/api/fb/app",{json:{app_id:$("#fb_id").value,app_secret:$("#fb_sec").value}});location.href="/api/fb/login"},"fbmsg");
  act("fb_disc",async()=>{ACC=await api("/api/fb/disconnect",{method:"POST"});renderAcc()},"fbmsg");
  act("fb_man",async()=>{ACC=await api("/api/fb/manual",{json:{page_id:$("#fb_pid").value,token:$("#fb_tok").value}});renderAcc();msg("fbmsg","ok","Conectado")},"fbmsg");
  const sel=$("#fb_page");if(sel)sel.onchange=async()=>{ACC=await api("/api/fb/page",{json:{id:sel.value}});renderAcc()};
  const ttSave=async()=>{ACC=await api("/api/tt/app",{json:{client_key:$("#tt_key").value,client_secret:$("#tt_sec").value,redirect_uri:$("#tt_red").value}})};
  act("tt_save",async()=>{await ttSave();renderAcc();msg("ttmsg","ok","Guardado")},"ttmsg");
  act("tt_login",async()=>{await ttSave();const r=await api("/api/tt/login");window.open(r.url,"_blank");msg("ttmsg","ok","Autoriza en la pestaña nueva y luego pega aquí la dirección final.")},"ttmsg");
  act("tt_fin",async()=>{ACC=await api("/api/tt/finish",{json:{pasted:$("#tt_paste").value}});renderAcc();msg("ttmsg","ok","¡TikTok conectado!")},"ttmsg");
  act("tt_disc",async()=>{ACC=await api("/api/tt/disconnect",{method:"POST"});renderAcc()},"ttmsg");
}

/* ---------- Ajustes ---------- */
async function loadSettingsTab(){
  CFG=await api("/api/config");ASSETS=await api("/api/assets");
  $("#aimask").textContent=CFG.ai?"· guardada "+CFG.ai_mask:"";$("#sttmask").textContent=CFG.stt?"· guardada "+CFG.stt_mask:"";
  renderSettings($("#set-def"),CFG.defaults);sysBadges();
  try{TPLS=await api("/api/templates")}catch(e){TPLS=[]}
  $("#tpls").innerHTML=TPLS.length?TPLS.map(t=>`<div class="q" style="margin:6px 0"><span>🎨 ${esc(t.name)}</span><span><button class="btn sec sm" data-tpluse="${esc(t.id)}">Usar por defecto</button> <button class="btn bad sm" data-tpldel="${esc(t.id)}">Borrar</button></span></div>`).join(""):'<div class="tiny">Todavía no hay plantillas.</div>';
  $("#assets").innerHTML=ASSETS.length?ASSETS.map(a=>`<div class="q" style="margin:6px 0"><span>${a.kind==="music"?"🎵":"🖼️"} ${esc(a.name)} <span class="tiny">${(a.size/1048576).toFixed(1)} MB</span></span><button class="btn bad sm" data-delasset="${esc(a.name)}">Borrar</button></div>`).join(""):'<div class="tiny">Nada subido.</div>';
  $("#status").innerHTML=[["FFmpeg",CFG.ffmpeg],["yt-dlp",CFG.ytdlp],["curl-cffi (Kick)",CFG.impers],["Fuente para textos",CFG.font],["Clave Anthropic",CFG.ai],["Clave OpenAI",CFG.stt]].map(([n,v])=>`${v?"✅":"❌"} ${n}`).join("<br>");
}
$("#savekeys").onclick=async()=>{try{CFG=await api("/api/config",{json:{anthropic_key:$("#k_ai").value,openai_key:$("#k_stt").value}});$("#k_ai").value=$("#k_stt").value="";$("#keymsg").innerHTML='<div class="msg ok">Guardado</div>';loadSettingsTab()}catch(e){$("#keymsg").innerHTML=`<div class="msg bad">${esc(e.message)}</div>`}};
$("#savedef").onclick=async()=>{try{CFG=await api("/api/config",{json:{defaults:$("#set-def").getSettings()}});renderSettings($("#set-new"),CFG.defaults);$("#defmsg").innerHTML='<div class="msg ok">Guardado</div>'}catch(e){$("#defmsg").innerHTML=`<div class="msg bad">${esc(e.message)}</div>`}};
$("#assetup").onclick=async()=>{const f=$("#assetfile").files[0];if(!f)return;const nm=prompt("Ponle un nombre para reconocerlo después:",f.name.replace(/\.[^.]+$/,""));if(nm===null)return;const fd=new FormData();fd.append("file",f);fd.append("label",nm);try{await api("/api/assets",{method:"POST",body:fd});$("#assetfile").value="";loadSettingsTab()}catch(e){alert(e.message)}};
$("#assets").onclick=async e=>{const b=e.target.closest("[data-delasset]");if(!b)return;if(confirm("¿Borrar?")){await api("/api/assets/"+encodeURIComponent(b.dataset.delasset),{method:"DELETE"});loadSettingsTab()}};

$("#tpls").onclick=async e=>{const u=e.target.dataset.tpluse,d=e.target.dataset.tpldel;
  try{if(d){TPLS=await api("/api/templates/"+d,{method:"DELETE"})}
    if(u){const t=TPLS.find(x=>x.id===u);CFG=await api("/api/config",{json:{defaults:t.settings}});$("#tplmsg").innerHTML='<div class="msg ok">Ahora es tu estilo por defecto.</div>'}}catch(er){$("#tplmsg").innerHTML=`<div class="msg bad">${esc(er.message)}</div>`}loadSettingsTab()};
$("#tpl_save").onclick=async()=>{const n=$("#tpl_name").value.trim();if(!n){$("#tplmsg").innerHTML='<div class="msg bad">Ponle un nombre.</div>';return}
  try{await api("/api/templates",{json:{name:n,settings:$("#set-def").getSettings()}});$("#tpl_name").value="";$("#tplmsg").innerHTML='<div class="msg ok">Plantilla guardada.</div>';loadSettingsTab()}catch(e){$("#tplmsg").innerHTML=`<div class="msg bad">${esc(e.message)}</div>`}};
boot();
</script>
</body>
</html>
"""


def main():
    n = load_jobs()
    q = load_queue()
    cleanup_old_jobs()
    threading.Thread(target=scheduler_loop, daemon=True).start()
    host = os.environ.get("HOST", "127.0.0.1")
    print(f"Lico Clips listo -> abre http://localhost:{PORT} en Chrome   ({n} trabajos guardados, {q} publicaciones en cola)")
    print("Tip: ejecuta 'termux-wake-lock' para que Android no duerma la app (necesario para publicaciones programadas).")
    app.run(host=host, port=PORT, threaded=True)


if __name__ == "__main__":
    main()
