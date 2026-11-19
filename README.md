#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Veridex - Multimodal Digital Forensics and Deepfake Detection System
INNOVEDGE HACKATHON 2026 - Problem Statement 04

SINGLE-FILE APPLICATION.   Run:   python app.py      then open http://127.0.0.1:5000
Self test:                         python app.py --selftest

Honesty notes (also shown in the UI):
 * Heuristic results are NEVER labelled as machine-learning predictions.
 * No random/invented confidence values. Heuristics have NO probability; only an
   optional pretrained model produces a score, and it is labelled "uncalibrated".
 * "No indicators detected" never guarantees authenticity; indicators are not proof.
 * Evidence tracking here is NOT legally certified chain-of-custody.
"""
import os, sys, io, re, json, uuid, time, base64, hashlib, sqlite3, threading, subprocess
import shutil, difflib, wave, traceback, logging, tempfile, webbrowser
from datetime import datetime, timezone, timedelta
from pathlib import Path

# 0. DEPENDENCY BOOTSTRAP (auto-installs missing pip packages once; set
#    VERIDEX_NO_INSTALL=1 to disable). Core = flask pillow numpy reportlab
def _ensure(mod, pip=None, required=False):
    try:
        __import__(mod); return True
    except ImportError:
        if os.environ.get("VERIDEX_NO_INSTALL"):
            if required: sys.exit("Missing required package: pip install " + (pip or mod))
            return False
        print(f"[setup] installing {pip or mod} ...")
        try:
            subprocess.check_call([sys.executable, "-m", "pip", "install", "-q", pip or mod])
            __import__(mod); return True
        except Exception as e:
            print(f"[setup] could not install {pip or mod}: {e}")
            if required: sys.exit("Install manually: pip install " + (pip or mod))
            return False

for _m, _p in [("flask", "flask"), ("PIL", "pillow"), ("numpy", "numpy"), ("reportlab", "reportlab")]:
    _ensure(_m, _p, required=True)
HAS_CV2 = _ensure("cv2", "opencv-python-headless")
HAS_SF = _ensure("soundfile", "soundfile")
HAS_LIBROSA = _ensure("librosa", "librosa")

import numpy as np
from PIL import Image, ImageDraw, ImageFilter, ExifTags
from flask import Flask, request, jsonify, Response, send_file, abort
from werkzeug.utils import secure_filename
if HAS_CV2: import cv2
if HAS_SF: import soundfile as sf
if HAS_LIBROSA:
    try: import librosa
    except Exception: HAS_LIBROSA = False

# 1. CONFIG
BASE = Path(__file__).resolve().parent
UPLOADS, PROCESSED, REPORTS, INSTANCE = (BASE / d for d in ("uploads", "processed", "reports", "instance"))
for _d in (UPLOADS, PROCESSED, REPORTS, INSTANCE): _d.mkdir(exist_ok=True)
DB_PATH = INSTANCE / "veridex.db"
MAX_UPLOAD = int(os.environ.get("VERIDEX_MAX_MB", "500")) * 1024 * 1024
MAX_VIDEO_FRAMES = 48          # frames sampled per video
MAX_AUDIO_SECONDS = 120        # audio analysed up to this length
VIDEO_TIME_LIMIT = 240         # seconds of processing allowed for a video
APP_VERSION = "1.0.0"
EXT = {"image": {"jpg", "jpeg", "png", "webp"}, "video": {"mp4", "avi", "mov", "mkv"},
       "audio": {"wav", "mp3", "m4a", "flac"}, "text": {"txt"}}
MIME = {"jpg": "image/jpeg", "jpeg": "image/jpeg", "png": "image/png", "webp": "image/webp",
        "mp4": "video/mp4", "avi": "video/x-msvideo", "mov": "video/quicktime", "mkv": "video/x-matroska",
        "wav": "audio/wav", "mp3": "audio/mpeg", "m4a": "audio/mp4", "flac": "audio/flac", "txt": "text/plain"}
LABELS = ["No significant indicators detected", "Potential manipulation detected", "Inconclusive",
          "Insufficient evidence", "Analysis unavailable"]
logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("veridex")
now = lambda: datetime.now(timezone.utc).isoformat(timespec="seconds")
ID_RE = re.compile(r"^[A-Za-z0-9_-]{6,40}$")

# 2. DATABASE (sqlite3, foreign keys + constraints)

SCHEMA = """
CREATE TABLE IF NOT EXISTS investigations(
  id TEXT PRIMARY KEY, title TEXT NOT NULL, created_at TEXT NOT NULL, status TEXT NOT NULL DEFAULT 'open');
CREATE TABLE IF NOT EXISTS uploaded_files(
  id TEXT PRIMARY KEY, investigation_id TEXT NOT NULL REFERENCES investigations(id) ON DELETE CASCADE,
  original_name TEXT NOT NULL, stored_name TEXT NOT NULL UNIQUE, kind TEXT NOT NULL
  CHECK(kind IN('image','video','audio','text')), ext TEXT NOT NULL, size INTEGER NOT NULL,
  sha256 TEXT NOT NULL, uploaded_at TEXT NOT NULL, status TEXT NOT NULL DEFAULT 'uploaded');
CREATE TABLE IF NOT EXISTS analysis_results(
  id INTEGER PRIMARY KEY AUTOINCREMENT, file_id TEXT NOT NULL REFERENCES uploaded_files(id) ON DELETE CASCADE,
  kind TEXT NOT NULL, label TEXT NOT NULL, method TEXT, model_name TEXT, model_version TEXT,
  score_type TEXT, score_value REAL, result_json TEXT NOT NULL, started_at TEXT, completed_at TEXT);
CREATE TABLE IF NOT EXISTS detected_indicators(
  id INTEGER PRIMARY KEY AUTOINCREMENT, analysis_id INTEGER NOT NULL REFERENCES analysis_results(id) ON DELETE CASCADE,
  name TEXT NOT NULL, description TEXT, severity TEXT NOT NULL, timestamp_sec REAL);
CREATE TABLE IF NOT EXISTS evidence_references(
  id INTEGER PRIMARY KEY AUTOINCREMENT, analysis_id INTEGER NOT NULL REFERENCES analysis_results(id) ON DELETE CASCADE,
  file_id TEXT NOT NULL, ref_type TEXT NOT NULL, ref_value TEXT NOT NULL, note TEXT);
CREATE TABLE IF NOT EXISTS cross_modal_findings(
  id INTEGER PRIMARY KEY AUTOINCREMENT, investigation_id TEXT NOT NULL REFERENCES investigations(id) ON DELETE CASCADE,
  relation TEXT NOT NULL, status TEXT NOT NULL, explanation TEXT, sources_json TEXT, created_at TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS forensic_reports(
  id INTEGER PRIMARY KEY AUTOINCREMENT, investigation_id TEXT NOT NULL REFERENCES investigations(id) ON DELETE CASCADE,
  pdf_name TEXT, json_name TEXT, created_at TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS audit_logs(
  id INTEGER PRIMARY KEY AUTOINCREMENT, investigation_id TEXT, event TEXT NOT NULL, detail TEXT, ts TEXT NOT NULL);
"""
_dblock = threading.Lock()

def db():
    c = sqlite3.connect(DB_PATH, timeout=30)
    c.row_factory = sqlite3.Row
    c.execute("PRAGMA foreign_keys=ON")
    return c

def q(sql, args=(), one=False, commit=False):
    """Run a query; returns rows (list of dict), a single dict, or lastrowid when commit=True."""
    with _dblock:
        c = db()
        try:
            cur = c.execute(sql, args)
            if commit:
                c.commit(); return cur.lastrowid
            rows = [dict(r) for r in cur.fetchall()]
            return (rows[0] if rows else None) if one else rows
        finally:
            c.close()

def init_db():
    with _dblock:
        c = db(); c.executescript(SCHEMA); c.commit(); c.close()

def audit(inv, event, detail=""):
    q("INSERT INTO audit_logs(investigation_id,event,detail,ts) VALUES(?,?,?,?)", (inv, event, str(detail)[:500], now()), commit=True)


# 3. SERVICES: hashing, validation, metadata, confidence
def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for ch in iter(lambda: f.read(1 << 20), b""): h.update(ch)
    return h.hexdigest()

def kind_of(ext):
    for k, s in EXT.items():
        if ext in s: return k
    return None

def validate_content(path, ext, kind):
    """Check real file content (magic bytes), not only the extension."""
    with open(path, "rb") as f: head = f.read(64)
    ok = False
    if kind == "image":
        ok = head[:3] == b"\xff\xd8\xff" if ext in ("jpg", "jpeg") else head[:8] == b"\x89PNG\r\n\x1a\n" if ext == "png" \
            else (head[:4] == b"RIFF" and head[8:12] == b"WEBP")
        if ok:
            try:
                with Image.open(path) as im: im.verify()
            except Exception: ok = False
    elif kind == "video":
        ok = (head[4:8] in (b"ftyp", b"moov", b"mdat", b"wide", b"free", b"skip") if ext in ("mp4", "mov")
              else head[:4] == b"RIFF" and head[8:12] == b"AVI " if ext == "avi" else head[:4] == b"\x1aE\xdf\xa3")
    elif kind == "audio":
        ok = (head[:4] == b"RIFF" and head[8:12] == b"WAVE" if ext == "wav" else head[:4] == b"fLaC" if ext == "flac"
              else head[4:8] == b"ftyp" if ext == "m4a" else head[:3] == b"ID3" or (head[0] == 0xFF and head[1] & 0xE0 == 0xE0))
    elif kind == "text":
        try:
            data = open(path, "rb").read(1 << 20); ok = b"\x00" not in data; data.decode("utf-8")
        except Exception: ok = False
    return ok

def exif_dict(im):
    out = {}
    try:
        ex = im.getexif()
        merged = dict(ex)
        try: merged.update(ex.get_ifd(0x8769))
        except Exception: pass
        for k, v in merged.items():
            name = ExifTags.TAGS.get(k, str(k))
            if isinstance(v, bytes): v = v[:40].decode("latin-1", "ignore")
            if isinstance(v, (str, int, float)) or hasattr(v, "numerator"): out[name] = str(v)[:120]
    except Exception: pass
    return out

def decide(inds, available=True, insufficient=False):
    """Qualitative label. Rules: 1 high OR >=2 medium -> potential manipulation; never from one weak signal."""
    if not available: return LABELS[4]
    if insufficient: return LABELS[3]
    sev = [i["severity"] for i in inds]
    hi, med, low = sev.count("high"), sev.count("medium"), sev.count("low")
    if hi or med >= 2: return LABELS[1]
    if med == 1 or low >= 2: return LABELS[2]
    return LABELS[0]

def make_result(kind, method, model, inds, limits, alts, available=True, insufficient=False, model_score=None, extra=None):
    """Common structured finding format used by every analyzer, the DB, correlation and reports."""
    label = decide(inds, available, insufficient)
    if model_score is not None:
        score = {"value": round(float(model_score), 4), "type": "UNCALIBRATED model score (not a probability)"}
    else:
        score = {"value": None, "type": "No calibrated probability available - qualitative assessment only"}
    flagged = [i for i in inds if i["severity"] in ("medium", "high")]
    if not available: expl = "The analysis could not be performed with the components available on this system."
    elif insufficient: expl = "The submitted evidence is too limited for a meaningful assessment."
    elif flagged or label == LABELS[2]:
        expl = "Flagged because: " + "; ".join(i["name"] for i in (flagged or inds) if i["severity"] != "info") + "."
    else: expl = "No significant indicators were found by the checks that were run."
    uncertainty = {LABELS[0]: "Absence of indicators does NOT guarantee authenticity; high-quality manipulations can evade these checks.",
                   LABELS[1]: "Indicators are evidence for human review, not proof. Alternative benign explanations exist (see below).",
                   LABELS[2]: "Evidence is weak or mixed. Human verification is required.",
                   LABELS[3]: "Not enough data to assess.", LABELS[4]: "No assessment was made."}[label]
    r = {"kind": kind, "label": label, "method": method, "model": model, "score": score, "indicators": inds,
         "explanation": expl, "uncertainty": uncertainty, "limitations": limits, "alternatives": alts,
         "disclaimer": "AI/heuristic output is not absolute proof. Not legally certified forensic analysis.",
         "analyzed_at": now()}
    r.update(extra or {})
    return r

def ind(name, desc, sev="low", ts=None, ref=None):
    return {"name": name, "description": desc, "severity": sev, "timestamp": ts, "ref": ref}

# 4. MODELS (optional pretrained models; lazy-loaded; never faked)
_models, _mlock = {}, threading.Lock()
IMAGE_MODEL_ID = os.environ.get("VERIDEX_IMAGE_MODEL", "umm-maybe/AI-image-detector")
AUDIO_MODEL_ID = os.environ.get("VERIDEX_AUDIO_MODEL", "")   # optional HF audio-classification model id

def load_pipeline(task, model_id):
    """Returns (pipeline|None, status_message). Needs: pip install torch transformers (+ internet once to download)."""
    key = (task, model_id)
    with _mlock:
        if key in _models: return _models[key]
        try:
            from transformers import pipeline
            p = pipeline(task, model=model_id)
            _models[key] = (p, "loaded")
        except ImportError: _models[key] = (None, "torch/transformers not installed")
        except Exception as e: _models[key] = (None, "model could not be loaded: " + type(e).__name__)
        return _models[key]

def image_model_scores(pil_img):
    p, msg = load_pipeline("image-classification", IMAGE_MODEL_ID)
    if p is None: return None, msg
    try: return p(pil_img.convert("RGB")), "ok"
    except Exception as e: return None, "inference failed: " + type(e).__name__

# 5. IMAGE ANALYZER
AI_RE = re.compile(r"stable.?diffusion|midjourney|dall[-\s·]?e|firefly|comfyui|automatic1111|novelai|invokeai|sdxl|leonardo\.ai|runwayml|ideogram|imagen", re.I)
EDIT_RE = re.compile(r"photoshop|gimp|lightroom|affinity|pixlr|canva|paint\.net|snapseed|facetune", re.I)

def b64img(im, fmt="JPEG", q_=82):
    b = io.BytesIO(); im.convert("RGB").save(b, fmt, quality=q_)
    return f"data:image/{fmt.lower()};base64," + base64.b64encode(b.getvalue()).decode()

def analyze_image(path, ctx=None):
    inds, limits = [], ["Error Level Analysis is noisy; it is most meaningful for JPEGs and can highlight legitimate sharp edges/text.",
                        "Metadata can be stripped or forged; missing metadata is NOT evidence of fakery.",
                        "No pixel-level localisation model is used; regions come from a heuristic."]
    alts = ["Legitimate editing (cropping, resizing, colour correction, recompression)", "Social-media re-encoding", "Screenshots or format conversion"]
    im0 = Image.open(path); fmt = im0.format
    meta = {"format": fmt, "width": im0.width, "height": im0.height, "mode": im0.mode}
    ex = exif_dict(im0); meta["exif"] = ex
    text_meta = {k: str(v)[:300] for k, v in im0.info.items() if isinstance(v, (str,)) }
    meta["embedded_text"] = {k: v for k, v in list(text_meta.items())[:10]}
    raw = open(path, "rb").read(5_000_000)
    # --- metadata observations
    blob = " ".join([ex.get("Software", ""), " ".join(text_meta.values())])
    m = AI_RE.search(blob)
    if m or b"trainedAlgorithmicMedia" in raw:
        inds.append(ind("Metadata references an AI generator", f"Embedded metadata contains '{m.group(0) if m else 'trainedAlgorithmicMedia (IPTC digital source type)'}'. Metadata is self-declared and can be forged or copied.", "high", ref={"type": "metadata", "value": "Software/embedded text/XMP"}))
    if b"c2pa" in raw or b"jumbf" in raw:
        inds.append(ind("Content Credentials (C2PA) data present", "A provenance manifest appears to be embedded. This TOOL DOES NOT VERIFY signatures; verify with an official C2PA validator.", "info"))
    if EDIT_RE.search(ex.get("Software", "")):
        inds.append(ind("Editing software recorded", f"Software tag: {ex.get('Software')}. Common for legitimate retouching/export.", "low", ref={"type": "metadata", "value": "EXIF Software"}))
    if not ex:
        inds.append(ind("No EXIF metadata", "No camera metadata found. This is common (screenshots, social media, privacy tools) and does NOT indicate manipulation.", "info"))
    try:
        d1 = datetime.strptime(ex.get("DateTime", "")[:19], "%Y:%m:%d %H:%M:%S"); d2 = datetime.strptime(ex.get("DateTimeOriginal", "")[:19], "%Y:%m:%d %H:%M:%S")
        if abs((d1 - d2).days) >= 1:
            inds.append(ind("Metadata timestamp discrepancy", f"File modified {d1} vs original capture {d2}; indicates later editing/saving (not necessarily manipulation).", "low", ref={"type": "metadata", "value": "EXIF DateTime"}))
    except Exception: pass
    w, h = im0.size
    if w == h and w in (256, 512, 768, 1024, 1536, 2048):
        inds.append(ind("Resolution typical of image generators", f"{w}x{h} square power-of-two size is common for generators but also for many legitimate images.", "info"))
    # --- ELA heuristic
    im = im0.convert("RGB"); im.thumbnail((1600, 1600))
    buf = io.BytesIO(); im.save(buf, "JPEG", quality=90); buf.seek(0)
    rec = Image.open(buf).convert("RGB")
    diff = np.abs(np.asarray(im, np.float32) - np.asarray(rec, np.float32)).mean(2)
    H, W = diff.shape; bs = max(16, min(H, W) // 24)
    gh, gw = H // bs, W // bs
    regions, art = [], {}
    if gh >= 3 and gw >= 3:
        bm = diff[:gh * bs, :gw * bs].reshape(gh, bs, gw, bs).mean((1, 3))
        med = float(np.median(bm)) + 1e-3; ratio = float(bm.max() / med)
        hot = np.argwhere(bm > max(med * 3, 1.5))
        order = sorted(hot.tolist(), key=lambda p: -bm[p[0], p[1]])[:6]
        for (r_, c_) in order:
            regions.append({"x": round(c_ * bs / W, 3), "y": round(r_ * bs / H, 3), "w": round(bs / W, 3), "h": round(bs / H, 3), "ela": round(float(bm[r_, c_]), 2)})
        frac = len(hot) / (gh * gw)
        if fmt == "JPEG" and ratio >= 4 and frac < 0.35 and regions:
            sev = "medium" if ratio >= 8 else "low"
            inds.append(ind("Localised error-level anomaly", f"{len(hot)} block(s) ({frac:.1%} of area) show recompression error {ratio:.1f}x the median. Possible local edit/composite OR high-contrast detail.", sev, ref={"type": "region", "value": json.dumps(regions[:3])}))
        elif fmt != "JPEG":
            limits.append(f"Source is {fmt}: ELA was computed for visualisation only and not used as an indicator.")
        heat = np.clip(diff / (np.percentile(diff, 99.5) + 1e-3), 0, 1)[..., None]
        over = np.asarray(im, np.float32) * (1 - 0.6 * heat) + np.array([255, 40, 60], np.float32) * 0.6 * heat
        ov = Image.fromarray(over.clip(0, 255).astype(np.uint8)); dr = ImageDraw.Draw(ov)
        for rg in regions[:6]:
            dr.rectangle([rg["x"] * W, rg["y"] * H, (rg["x"] + rg["w"]) * W, (rg["y"] + rg["h"]) * H], outline=(0, 229, 255), width=2)
        art["heatmap"] = b64img(ov)
    # --- pretrained model (optional)
    model = {"name": IMAGE_MODEL_ID, "version": "HuggingFace hub (latest revision)", "type": "pretrained image classifier (AI-generated vs human)"}
    scores, msg = image_model_scores(Image.open(path)); mscore = None
    if scores:
        top = max(scores, key=lambda s: s["score"])
        art["model_output"] = [{"label": s["label"], "score": round(s["score"], 4)} for s in scores]
        ai = [s for s in scores if re.search(r"artificial|ai|fake|synthetic|generated", s["label"], re.I) and not re.search(r"^human|real", s["label"], re.I)]
        if ai:
            mscore = ai[0]["score"]
            if mscore >= 0.8:
                inds.append(ind("Pretrained detector favours AI-generated", f"Model label '{ai[0]['label']}' score {mscore:.3f} (uncalibrated; models often fail on new generators and re-compressed images).", "medium", ref={"type": "model", "value": IMAGE_MODEL_ID}))
        limits.append("Pretrained classifier scores are uncalibrated and may not generalise to unseen generators.")
    else:
        model = {"name": "Not used", "version": "-", "type": "Pretrained detector unavailable: " + msg + ". Install: pip install torch transformers"}
        limits.append("No pretrained AI-image detector was available; result relies on metadata and ELA heuristics only.")
    method = "Metadata inspection + Error Level Analysis (heuristic)" + (" + pretrained classifier" if scores else "")
    meta["regions"] = regions
    r = make_result("image", method, model, inds, limits, alts, model_score=mscore, extra={"metadata": meta, "flagged": [{"type": "region", **x} for x in regions[:3]] if any(i["name"].startswith("Localised") for i in inds) else [], **art})
    return r

# 6. VIDEO ANALYZER (OpenCV; FFmpeg fallback for container problems)
def robust_z(a):
    a = np.asarray(a, float); med = np.median(a); mad = np.median(np.abs(a - med)) * 1.4826 + 1e-6
    return (a - med) / mad

def ffmpeg_ok(): return shutil.which("ffmpeg") is not None

def analyze_video(path, ctx=None):
    limits = ["Frames are sampled sparsely; short manipulations can be missed and natural scene cuts look like discontinuities.",
              "No pretrained deepfake VIDEO model is bundled; face checks use Haar-cascade detection + statistics (heuristic).",
              "Lip-sync and physiological (blink/pulse) analysis are not implemented."]
    alts = ["Natural scene changes / editing cuts", "Heavy compression or resizing", "Beauty filters or stabilisation", "Occlusion or head turns"]
    if not HAS_CV2:
        return make_result("video", "unavailable", {"name": "OpenCV missing", "version": "-", "type": "-"}, [], limits, alts, available=False)
    tmp = None; cap = cv2.VideoCapture(str(path))
    if not cap.isOpened() or cap.get(cv2.CAP_PROP_FRAME_COUNT) <= 0:
        if ffmpeg_ok():   # transcode a working copy (original untouched)
            tmp = Path(tempfile.mkdtemp(dir=PROCESSED)) / "copy.mp4"
            subprocess.run(["ffmpeg", "-y", "-loglevel", "error", "-i", str(path), "-an", "-t", "120", str(tmp)], timeout=180)
            cap = cv2.VideoCapture(str(tmp))
    try:
        n = int(cap.get(cv2.CAP_PROP_FRAME_COUNT)); fps = cap.get(cv2.CAP_PROP_FPS) or 0
        w, h = int(cap.get(3)), int(cap.get(4))
        if n <= 0 or fps <= 0 or w <= 0:
            return make_result("video", "unavailable", {"name": "OpenCV", "version": cv2.__version__, "type": "-"}, [], limits, alts, available=False)
        fourcc = "".join(chr((int(cap.get(cv2.CAP_PROP_FOURCC)) >> 8 * i) & 0xFF) for i in range(4)).strip()
        meta = {"frames": n, "fps": round(fps, 3), "width": w, "height": h, "duration_sec": round(n / fps, 2), "codec": fourcc, "ffmpeg_available": ffmpeg_ok()}
        idxs = np.unique(np.linspace(0, n - 1, min(MAX_VIDEO_FRAMES, n)).astype(int))
        cascade = cv2.CascadeClassifier(os.path.join(getattr(cv2.data, "haarcascades", ""), "haarcascade_frontalface_default.xml"))
        if cascade.empty():   # some OpenCV builds ship without cascade files -> degrade gracefully
            cascade = None; limits.append("Face detector data not found in this OpenCV build; face-based checks were skipped.")
        rows, prev, t0 = [], None, time.time()
        for i in idxs:
            if time.time() - t0 > VIDEO_TIME_LIMIT:
                limits.append("Processing time limit reached; remaining frames skipped."); break
            cap.set(cv2.CAP_PROP_POS_FRAMES, int(i)); ok, fr = cap.read()
            if not ok: continue
            g = cv2.cvtColor(fr, cv2.COLOR_BGR2GRAY)
            sharp = float(cv2.Laplacian(g, cv2.CV_64F).var())
            hist = cv2.calcHist([g], [0], None, [64], [0, 256]); hist = cv2.normalize(hist, hist, norm_type=cv2.NORM_L1).flatten()
            d = float(cv2.compareHist(prev.astype(np.float32), hist.astype(np.float32), cv2.HISTCMP_BHATTACHARYYA)) if prev is not None else 0.0
            prev = hist
            faces = cascade.detectMultiScale(g, 1.1, 5, minSize=(max(40, w // 20),) * 2) if cascade is not None else []
            ratio, fb = None, None
            if len(faces):
                x, y, fw, fh = max(faces, key=lambda f: f[2] * f[3]); fb = [int(x), int(y), int(fw), int(fh)]
                ratio = float(cv2.Laplacian(g[y:y + fh, x:x + fw], cv2.CV_64F).var() / (sharp + 1e-6))
            sc = 320 / max(w, 1); small = cv2.resize(fr, (320, max(1, int(h * sc))))
            if fb: cv2.rectangle(small, tuple(int(v * sc) for v in fb[:2]), (int((fb[0] + fb[2]) * sc), int((fb[1] + fb[3]) * sc)), (255, 229, 0), 2)
            _, jb = cv2.imencode(".jpg", small, [cv2.IMWRITE_JPEG_QUALITY, 80])
            rows.append({"frame": int(i), "time": round(i / fps, 2), "sharp": round(sharp, 2), "diff": round(d, 4), "face": bool(fb), "ratio": ratio, "jpg": jb.tobytes(), "flags": []})
    finally:
        cap.release()
        if tmp: shutil.rmtree(tmp.parent, ignore_errors=True)
    inds = []
    if len(rows) < 4:
        return make_result("video", "Frame statistics", {"name": "OpenCV", "version": cv2.__version__, "type": "heuristic"}, [], limits, alts, insufficient=True, extra={"metadata": meta})
    # (a) abrupt visual discontinuities
    dz = robust_z([r["diff"] for r in rows])
    for r_, z in zip(rows, dz):
        if z > 4 and r_["diff"] > 0.15: r_["flags"].append("Abrupt visual discontinuity")
    # (b) face-region sharpness inconsistent with the rest of the video
    fr_rows = [r for r in rows if r["ratio"] is not None]
    if len(fr_rows) >= 6:
        zr = robust_z([np.log(r["ratio"] + 1e-6) for r in fr_rows])
        for r_, z in zip(fr_rows, zr):
            if abs(z) > 3.5: r_["flags"].append("Face-region sharpness inconsistent")
    # (c) face detection drop-outs between frames where a face is present
    for k in range(1, len(rows) - 1):
        if not rows[k]["face"] and rows[k - 1]["face"] and rows[k + 1]["face"]: rows[k]["flags"].append("Face detection drop-out")
    groups = {}
    for r_ in rows:
        for fl in r_["flags"]: groups.setdefault(fl, []).append(r_)
    desc = {"Abrupt visual discontinuity": ("Large luminance-histogram change between sampled frames (possible cut/splice; natural scene change is common).", "low"),
            "Face-region sharpness inconsistent": ("Face sharpness relative to the frame differs strongly from other frames (possible blending/smoothing; also caused by motion blur or focus).", "medium" if len(groups.get("Face-region sharpness inconsistent", [])) >= 3 else "low"),
            "Face detection drop-out": ("A face tracked in neighbouring frames is missing in between (possible instability of a face region; also occlusion/head turn).", "low")}
    for name, lst in groups.items():
        d_, sev = desc[name]
        inds.append(ind(name, f"{d_} Occurrences: {len(lst)} frame(s).", sev, ts=lst[0]["time"], ref={"type": "frame", "value": ", ".join(f"#{x['frame']}@{x['time']}s" for x in lst[:8])}))
    # optional: run image detector on a few frames (clearly labelled as per-frame image classifier)
    model = {"name": "Not used (no pretrained video deepfake model bundled)", "version": "-", "type": "OpenCV Haar cascade + statistical heuristics"}
    mscore = None
    p, msg = load_pipeline("image-classification", IMAGE_MODEL_ID) if os.environ.get("VERIDEX_VIDEO_FRAME_MODEL") else (None, "")
    if p:
        sc_ = []
        for r_ in rows[:: max(1, len(rows) // 6)][:6]:
            res = p(Image.open(io.BytesIO(r_["jpg"])).convert("RGB"))
            a = [s["score"] for s in res if re.search(r"artificial|fake|ai", s["label"], re.I)]
            if a: sc_.append(a[0])
        if sc_:
            mscore = float(np.mean(sc_)); model = {"name": IMAGE_MODEL_ID, "version": "HF latest", "type": "per-frame IMAGE classifier (not a video deepfake model)"}
            if mscore >= 0.8: inds.append(ind("Per-frame image detector favours AI-generated", f"Mean uncalibrated score {mscore:.3f} over {len(sc_)} frames.", "medium"))
    flagged = [r for r in rows if r["flags"]][:16]
    out_frames = [{"frame": r["frame"], "time": r["time"], "thumb": "data:image/jpeg;base64," + base64.b64encode(r["jpg"]).decode(),
                   "indicators": r["flags"], "note": f"sharpness={r['sharp']}, histogram-diff={r['diff']}" + (f", face/frame sharpness ratio={r['ratio']:.2f}" if r["ratio"] else ""),
                   "confidence": "Qualitative: heuristic flag (no calibrated probability)"} for r in flagged]
    timeline = [{"t": r["time"], "diff": r["diff"], "sharp": r["sharp"], "flag": bool(r["flags"])} for r in rows]
    meta["frames_analyzed"] = len(rows)
    ext = {"metadata": meta, "frames_flagged": out_frames, "timeline": timeline,
           "flagged": [{"type": "frame", "frame": f["frame"], "time": f["time"]} for f in out_frames],
           "frame_summary": f"{len(rows)} frames sampled, {len(flagged)} flagged ({len(flagged) / len(rows):.0%}). A single flagged frame never classifies the whole video."}
    # an entire video is only 'potential manipulation' when several independent indicators agree (decide())
    return make_result("video", "Frame sampling + visual-consistency & face statistics (heuristic)", model, inds, limits, alts, model_score=mscore, extra=ext)

# 7. AUDIO ANALYZER (soundfile/librosa/FFmpeg loaders; numpy spectral analysis)
def load_audio(path):
    """Return (mono float32 samples, sr, info). Tries soundfile -> librosa -> ffmpeg->wav -> wave."""
    errs = []
    def via_sf(p):
        with sf.SoundFile(str(p)) as f:
            sr, tot, ch = f.samplerate, len(f), f.channels
            y = f.read(min(tot, sr * MAX_AUDIO_SECONDS), dtype="float32", always_2d=True)
        return y.mean(1), sr, {"channels": ch, "total_duration": tot / sr}
    if HAS_SF:
        try: return via_sf(path)
        except Exception as e: errs.append(e)
    if HAS_LIBROSA:
        try:
            y, sr = librosa.load(str(path), sr=None, mono=True, duration=MAX_AUDIO_SECONDS)
            return y.astype(np.float32), sr, {"channels": None, "total_duration": librosa.get_duration(path=str(path))}
        except Exception as e: errs.append(e)
    if ffmpeg_ok():
        tmpd = Path(tempfile.mkdtemp(dir=PROCESSED)); out = tmpd / "c.wav"
        try:
            subprocess.run(["ffmpeg", "-y", "-loglevel", "error", "-i", str(path), "-t", str(MAX_AUDIO_SECONDS), str(out)], timeout=120, check=True)
            if HAS_SF: return via_sf(out)
            return wav_read(out)
        except Exception as e: errs.append(e)
        finally: shutil.rmtree(tmpd, ignore_errors=True)
    if str(path).lower().endswith(".wav"):
        try: return wav_read(path)
        except Exception as e: errs.append(e)
    raise RuntimeError("Audio could not be decoded (" + "; ".join(type(e).__name__ for e in errs) + "). Install ffmpeg or soundfile/librosa.")

def wav_read(path):
    with wave.open(str(path), "rb") as wf:
        sr, ch, sw = wf.getframerate(), wf.getnchannels(), wf.getsampwidth()
        raw = wf.readframes(min(wf.getnframes(), sr * MAX_AUDIO_SECONDS))
        tot = wf.getnframes() / sr
    dt = {1: np.uint8, 2: np.int16, 4: np.int32}[sw]
    y = np.frombuffer(raw, dt).astype(np.float32)
    y = (y - 128) / 128 if sw == 1 else y / float(2 ** (8 * sw - 1))
    return y.reshape(-1, ch).mean(1), sr, {"channels": ch, "total_duration": tot}

def stft_mag(y, n=1024, hop=256):
    """Chunked numpy STFT magnitude (frames x bins)."""
    if len(y) < n: y = np.pad(y, (0, n - len(y)))
    win = np.hanning(n).astype(np.float32); view = np.lib.stride_tricks.sliding_window_view(y, n)[::hop]
    out = [np.abs(np.fft.rfft(view[i:i + 2000] * win, axis=1)).astype(np.float32) for i in range(0, len(view), 2000)]
    return np.vstack(out)

def transcribe(path):
    """Offline transcription with openai-whisper if installed (pip install openai-whisper). Otherwise None."""
    try: import whisper
    except ImportError: return None
    try:
        m = whisper.load_model(os.environ.get("VERIDEX_WHISPER", "tiny")); r = m.transcribe(str(path))
        return {"text": r["text"].strip(), "engine": "openai-whisper/" + os.environ.get("VERIDEX_WHISPER", "tiny"),
                "segments": [{"start": round(s["start"], 2), "end": round(s["end"], 2), "text": s["text"].strip()} for s in r["segments"]]}
    except Exception as e: return {"error": type(e).__name__ + ": " + str(e)[:120]}

def analyze_audio(path, ctx=None):
    limits = ["Spectral/continuity checks are heuristics; they cannot identify voice cloning on their own.",
              "Lossy codecs, noise gates, normalisation and telephone bandwidth produce many of the same patterns.",
              f"Only the first {MAX_AUDIO_SECONDS}s are analysed."]
    alts = ["Lossy compression (MP3/AAC) or resampling", "Noise gating / denoising", "Studio processing", "Edited-but-genuine recording"]
    try: y, sr, info = load_audio(path)
    except Exception as e:
        return make_result("audio", "unavailable", {"name": "decoders", "version": "-", "type": "-"}, [], limits + [str(e)], alts, available=False)
    dur = len(y) / sr; inds = []
    meta = {"sample_rate": sr, "channels": info["channels"], "duration_sec": round(dur, 2), "total_duration_sec": round(info["total_duration"], 2), "librosa": HAS_LIBROSA, "soundfile": HAS_SF}
    if dur < 1.0:
        return make_result("audio", "Spectral analysis", {"name": "numpy STFT", "version": np.__version__, "type": "heuristic"}, [], limits, alts, insufficient=True, extra={"metadata": meta})
    peak = float(np.abs(y).max()) + 1e-9; y = y / peak if peak > 1 else y
    hop = max(256, len(y) // 20000); n = 1024
    mag = stft_mag(y, n, hop); ft = hop / sr
    pw = mag ** 2; edb = 10 * np.log10(pw.sum(1) + 1e-12)
    freqs = np.fft.rfftfreq(n, 1 / sr)
    flat = np.exp(np.log(mag + 1e-10).mean(1)) / (mag.mean(1) + 1e-10)
    cent = (mag * freqs).sum(1) / (mag.sum(1) + 1e-10)
    active = edb > (np.percentile(edb, 95) - 40)
    meta.update({"spectral_flatness_mean": round(float(flat[active].mean()) if active.any() else 0, 4),
                 "spectral_centroid_hz_mean": round(float(cent[active].mean()) if active.any() else 0, 1),
                 "peak_level": round(peak, 4), "noise_floor_db": round(float(np.percentile(edb, 10)), 1)})
    # (a) spectral bandwidth cut-off
    if active.any():
        ms = 20 * np.log10(mag[active].mean(0) + 1e-10); idx = np.where(ms > ms.max() - 70)[0]; cut = float(freqs[idx.max()]) if len(idx) else sr / 2
        meta["spectral_cutoff_hz"] = round(cut, 0)
        if sr >= 32000 and cut < 0.55 * sr / 2:
            inds.append(ind("Band-limited spectrum", f"Energy ends near {cut:.0f} Hz although sample rate is {sr} Hz (upsampled/lossy source or some synthesis pipelines).", "low", ref={"type": "spectral", "value": f"cutoff={cut:.0f}Hz"}))
    # (b) digital silence runs
    z = np.abs(y) < 1e-6; runs, start = [], None
    for i in np.flatnonzero(np.diff(np.concatenate([[0], z.astype(int), [0]]))):
        if start is None: start = i
        else:
            if (i - start) / sr >= 0.05 and start > sr * 0.1 and i < len(y) - sr * 0.1: runs.append((start / sr, i / sr))
            start = None
    if runs:
        inds.append(ind("Exact digital silence inside recording", f"{len(runs)} gap(s) of exact zeros (>=50 ms), first at {runs[0][0]:.2f}s. May indicate cuts/splices or a hard noise gate.", "low" if len(runs) < 3 else "medium", ts=round(runs[0][0], 2), ref={"type": "timestamp", "value": ", ".join(f"{a:.2f}-{b:.2f}s" for a, b in runs[:6])}))
    # (c) abrupt mid-sound energy discontinuities
    med_act = float(np.median(edb[active])) if active.any() else -60; jumps = []
    d = np.diff(edb)
    for k in np.flatnonzero(np.abs(d) > 20):
        if min(edb[k], edb[k + 1]) > med_act - 15: jumps.append(round((k + 1) * ft, 2))
    if jumps:
        inds.append(ind("Abrupt level discontinuities", f"{len(jumps)} sudden level change(s) inside active sound, first at {jumps[0]}s (possible splice; also plosives/clicks).", "low" if len(jumps) < 3 else "medium", ts=jumps[0], ref={"type": "timestamp", "value": ", ".join(f"{t}s" for t in jumps[:8])}))
    if meta["noise_floor_db"] < -100:
        inds.append(ind("Unusually clean noise floor", "Background noise is almost absent (consistent with synthetic audio OR heavy denoising/gating).", "low"))
    # optional pretrained synthetic-speech model
    model = {"name": "Not used", "version": "-", "type": "Spectral heuristics (numpy STFT)" + (" + librosa loader" if HAS_LIBROSA else "")}
    mscore, mout = None, None
    if AUDIO_MODEL_ID:
        p, msg = load_pipeline("audio-classification", AUDIO_MODEL_ID)
        if p:
            try:
                mout = p(str(path)); model = {"name": AUDIO_MODEL_ID, "version": "HF latest", "type": "pretrained audio classifier (labels as defined by model author)"}
                sy = [s for s in mout if re.search(r"fake|spoof|synth|ai|deepfake", s["label"], re.I)]
                if sy:
                    mscore = sy[0]["score"]
                    if mscore >= 0.8: inds.append(ind("Pretrained audio detector favours synthetic", f"Label '{sy[0]['label']}' score {mscore:.3f} (uncalibrated).", "medium"))
            except Exception as e: limits.append("Audio model inference failed: " + type(e).__name__)
        else: limits.append("Audio model unavailable: " + msg)
    else: limits.append("No pretrained synthetic-speech model configured (set VERIDEX_AUDIO_MODEL to a Hugging Face audio-classification model id).")
    tr = transcribe(path)
    if tr is None: limits.append("No transcription engine installed (pip install openai-whisper). Transcript unavailable.")
    elif "error" in tr: limits.append("Transcription failed: " + tr["error"]); tr = None
    # waveform + spectrogram artifacts
    npk = 800; ch = np.array_split(np.abs(y), npk); wave_pk = [round(float(c.max()) if len(c) else 0, 4) for c in ch]
    lg = np.log10(mag.T + 1e-6)                                   # bins x frames
    sp = np.array([x.mean(0) for x in np.array_split(lg, 128, axis=0) if len(x)])
    sp = np.array([x.mean(1) for x in np.array_split(sp, min(800, sp.shape[1]), axis=1) if x.shape[1]]).T
    s_db = 20 * sp; v = np.clip((s_db - (s_db.max() - 80)) / 80, 0, 1)[::-1]
    rgb = np.stack([v ** 2 * 255, np.clip(v * 1.4, 0, 1) ** 2 * 230, 60 + 195 * np.sqrt(v) * (1 - 0.5 * v)], -1).astype(np.uint8)
    spec = Image.fromarray(rgb).resize((800, 256))
    flagged = [{"type": "audio_segment", "start": t, "end": round(t + 0.3, 2), "reason": "level discontinuity"} for t in jumps[:10]] + \
              [{"type": "audio_segment", "start": round(a, 2), "end": round(b, 2), "reason": "digital silence"} for a, b in runs[:10]]
    ext = {"metadata": meta, "waveform": wave_pk, "spectrogram": b64img(spec, "PNG"), "transcript": tr, "flagged": flagged,
           "model_output": mout, "spectral_observations": [f"Sample rate {sr} Hz, duration {dur:.1f}s, mean spectral flatness {meta['spectral_flatness_mean']}, mean centroid {meta['spectral_centroid_hz_mean']} Hz, noise floor {meta['noise_floor_db']} dB."]}
    return make_result("audio", "Spectral/continuity heuristics" + (" + pretrained model" if mscore is not None else ""), model, inds, limits, alts, model_score=mscore, extra=ext)

# 8. TEXT ANALYZER (rule-based NLP heuristics)
SENS = ["breaking", "shocking", "unbelievable", "exposed", "they don't want you to know", "100%", "guaranteed", "miracle", "secret", "urgent", "share before", "must watch", "leaked", "cover-up", "you won't believe"]
ATTR = ["sources say", "reportedly", "allegedly", "experts say", "people are saying", "it is said", "rumor", "rumour", "insiders"]
TOK = lambda s: re.findall(r"[a-z0-9']+", s.lower())

def similarity(a, b):
    ta, tb = set(TOK(a)), set(TOK(b))
    if not ta or not tb: return 0.0
    jac = len(ta & tb) / len(ta | tb); seq = difflib.SequenceMatcher(None, TOK(a)[:600], TOK(b)[:600]).ratio()
    return round(max(jac, seq), 3)

def analyze_text(path, ctx=None):
    ctx = ctx or {}; text = open(path, encoding="utf-8", errors="replace").read()
    limits = ["Rule-based language heuristics only; no fact-checking against external sources.",
              "Text is NOT assumed to be misinformation because it is sensational or AI-written.",
              "Image/video content is not semantically understood (no captioning model); comparison uses metadata and transcripts only."]
    alts = ["Normal journalistic or marketing style", "Opinion writing", "Imperfect transcription (for transcript comparison)"]
    words = TOK(text); sents = [s.strip() for s in re.split(r"(?<=[.!?])\s+|\n+", text) if s.strip()]
    meta = {"characters": len(text), "words": len(words), "sentences": len(sents)}
    model = {"name": "Not used", "version": "-", "type": "Rule-based NLP heuristics"}
    if len(words) < 15:
        return make_result("text", "Rule-based text analysis", model, [], limits, alts, insufficient=True, extra={"metadata": meta, "highlights": []})
    inds, hl = [], []
    low = text.lower()
    sens = [w for w in SENS if w in low]; attr = [w for w in ATTR if w in low]
    if sens: inds.append(ind("Sensational / urgency language", "Phrases: " + ", ".join(sens), "medium" if len(sens) >= 3 else "low", ref={"type": "text", "value": ", ".join(sens)}))
    if attr: inds.append(ind("Unverifiable attribution", "Vague sourcing: " + ", ".join(attr), "low", ref={"type": "text", "value": ", ".join(attr)}))
    for s in sents:
        ls = s.lower(); hit = [w for w in sens + attr if w in ls]
        if hit: hl.append({"sentence": s[:300], "reason": "Suspicious claim wording: " + ", ".join(hit)})
    pairs = {}
    for num, noun in re.findall(r"\b(\d[\d,\.]*)\s+([a-zA-Z]{4,})", text): pairs.setdefault(noun.lower(), set()).add(num.rstrip(".,"))
    for noun, nums in pairs.items():
        if len(nums) > 1 and noun not in ("years", "year", "days", "hours", "minutes", "percent"):
            inds.append(ind("Possible internal numeric inconsistency", f"Different quantities stated for '{noun}': {', '.join(sorted(nums))} (may be different contexts).", "low", ref={"type": "text", "value": noun}))
            for s in sents:
                if noun in s.lower() and any(x in s for x in nums): hl.append({"sentence": s[:300], "reason": f"Differing numbers for '{noun}'"})
            break
    years = sorted(set(re.findall(r"\b(?:19|20)\d{2}\b", text)))
    meta["years_mentioned"] = years
    tr = ctx.get("transcript")
    if tr:
        sim = similarity(text, tr); meta["transcript_similarity"] = sim
        if sim < 0.25:
            inds.append(ind("Text does not match audio transcript", f"Token similarity {sim:.2f} with the transcript of the audio in this investigation (low).", "medium", ref={"type": "transcript", "value": f"similarity={sim}"}))
            missing = [w for w in dict.fromkeys(TOK(text)) if w not in set(TOK(tr)) and len(w) > 4][:15]
            hl.append({"sentence": "Words absent from transcript: " + ", ".join(missing), "reason": "Transcript mismatch"})
    else: limits.append("No audio transcript available in this investigation, so transcript comparison was skipped.")
    return make_result("text", "Rule-based NLP heuristics", model, inds, limits, alts, extra={"metadata": meta, "highlights": hl[:20]})

ANALYZERS = {"image": analyze_image, "video": analyze_video, "audio": analyze_audio, "text": analyze_text}

# 9. CORRELATION ENGINE (only compares evidence inside the SAME investigation)

def latest_results(inv_id):
    rows = q("""SELECT f.id fid,f.original_name,f.kind,f.sha256,r.result_json,r.id aid FROM uploaded_files f
                JOIN analysis_results r ON r.file_id=f.id WHERE f.investigation_id=? ORDER BY r.id""", (inv_id,))
    latest = {}
    for r in rows: latest[r["fid"]] = {**r, "result": json.loads(r["result_json"])}
    return list(latest.values())

def times_of(res, key):
    return [x.get("time", x.get("start")) for x in res.get("flagged", []) if x.get("type") == key and x.get("time", x.get("start")) is not None]

def correlate(inv_id):
    items = latest_results(inv_id); by = {}
    for it in items: by.setdefault(it["kind"], []).append(it)
    sources = [{"file": i["original_name"], "file_id": i["fid"], "kind": i["kind"], "finding": i["result"]["label"],
                "indicators": [x["name"] for x in i["result"]["indicators"] if x["severity"] != "info"]} for i in items]
    rel = []
    def add(name, status, expl, srcs): rel.append({"relation": name, "status": status, "explanation": expl, "sources": srcs})
    if len(items) < 2:
        add("Overall", "insufficient", "At least two analysed files of different types are needed for cross-modal correlation.", [])
    else:
        # video <-> audio
        for v in by.get("video", []):
            for a in by.get("audio", []):
                vm, am = v["result"].get("metadata", {}), a["result"].get("metadata", {})
                vt, at = times_of(v["result"], "frame"), times_of(a["result"], "audio_segment")
                src = [v["original_name"], a["original_name"]]
                dv, da = vm.get("duration_sec"), am.get("total_duration_sec")
                if dv and da:
                    if abs(dv - da) > 2: add("Video/audio duration", "contradictory", f"Video lasts {dv}s but audio lasts {da}s (difference {abs(dv - da):.1f}s). The pair may not belong together or one was trimmed.", src)
                    else: add("Video/audio duration", "supporting", f"Durations are consistent ({dv}s vs {da}s). This shows compatibility, not authenticity.", src)
                if vt and at:
                    near = [(x, y) for x in vt for y in at if abs(x - y) <= 1.5]
                    if near: add("Video/audio flagged timestamps", "supporting", f"{len(near)} flagged video/audio moments coincide within 1.5s (e.g. video {near[0][0]}s, audio {near[0][1]}s) - consistent with a possible joint edit, but could be coincidence.", src)
                    else: add("Video/audio flagged timestamps", "contradictory", "Flagged moments in the video and audio do not coincide; the indicators are independent.", src)
                else: add("Video/audio flagged timestamps", "insufficient", "One of the files has no flagged timestamps to compare.", src)
                add("Lip-sync (speech/mouth timing)", "insufficient", "Lip-sync analysis is not implemented in this version; no claim is made.", src)
        # audio transcript <-> text
        for a in by.get("audio", []):
            tr = (a["result"].get("transcript") or {}).get("text")
            for t in by.get("text", []):
                src = [a["original_name"], t["original_name"]]
                if not tr: add("Audio transcript vs text", "insufficient", "No transcript could be generated (install openai-whisper), so spoken words cannot be compared.", src); continue
                txt = open(UPLOADS / q("SELECT stored_name FROM uploaded_files WHERE id=?", (t["fid"],), one=True)["stored_name"], encoding="utf-8", errors="replace").read()
                s = similarity(tr, txt)
                add("Audio transcript vs text", "supporting" if s >= 0.6 else "contradictory" if s < 0.25 else "insufficient", f"Transcript/text similarity {s:.2f}." + (" Strong agreement." if s >= .6 else " Major mismatch." if s < .25 else " Partial overlap; inconclusive."), src)
        # image/video metadata year vs text claimed years
        for t in by.get("text", []):
            years = set(t["result"].get("metadata", {}).get("years_mentioned", []))
            for m in by.get("image", []):
                ex = m["result"].get("metadata", {}).get("exif", {}); y = (ex.get("DateTimeOriginal") or "")[:4]
                src = [m["original_name"], t["original_name"]]
                if y and years: add("Image capture year vs text", "supporting" if y in years else "contradictory", f"EXIF capture year {y}; text mentions {', '.join(sorted(years))}." + ("" if y in years else " Text may describe a different time (or EXIF is wrong)."), src)
                else: add("Image metadata vs description", "insufficient", "Image has no capture date or the text states no year; description cannot be checked against metadata. Visual content is not semantically analysed.", src)
        # cross-file pattern
        flagged = [s for s in sources if s["finding"] == LABELS[1]]
        if len(flagged) >= 2: add("Multi-source pattern", "supporting", f"{len(flagged)} independent sources show potential-manipulation indicators: " + ", ".join(s["file"] for s in flagged) + ". Agreement strengthens, but does not prove, concern.", [s["file"] for s in flagged])
        elif len(flagged) == 1: add("Multi-source pattern", "contradictory", f"Only '{flagged[0]['file']}' is flagged; other sources show no corroborating indicators.", [flagged[0]["file"]])
        else: add("Multi-source pattern", "neutral", "No source shows potential-manipulation indicators; this does not guarantee authenticity.", [])
    summ = {"supporting": sum(r["status"] == "supporting" for r in rel), "contradictory": sum(r["status"] == "contradictory" for r in rel), "insufficient": sum(r["status"] == "insufficient" for r in rel)}
    note = "Relationships are only evaluated between files the user placed in the same investigation; Veridex does not verify that they truly belong together."
    q("DELETE FROM cross_modal_findings WHERE investigation_id=?", (inv_id,), commit=True)
    for r in rel: q("INSERT INTO cross_modal_findings(investigation_id,relation,status,explanation,sources_json,created_at) VALUES(?,?,?,?,?,?)", (inv_id, r["relation"], r["status"], r["explanation"], json.dumps(r["sources"]), now()), commit=True)
    audit(inv_id, "correlation_run", json.dumps(summ))
    return {"investigation_id": inv_id, "sources": sources, "relations": rel, "summary": summ, "note": note}

# 10. JOBS + PERSISTENCE
JOBS = {}

def save_result(fid, r, started):
    m = r["model"]
    aid = q("INSERT INTO analysis_results(file_id,kind,label,method,model_name,model_version,score_type,score_value,result_json,started_at,completed_at) VALUES(?,?,?,?,?,?,?,?,?,?,?)",
            (fid, r["kind"], r["label"], r["method"], m["name"], m["version"], r["score"]["type"], r["score"]["value"], json.dumps(r), started, now()), commit=True)
    for i in r["indicators"]:
        q("INSERT INTO detected_indicators(analysis_id,name,description,severity,timestamp_sec) VALUES(?,?,?,?,?)", (aid, i["name"], i["description"], i["severity"], i.get("timestamp")), commit=True)
        if i.get("ref"): q("INSERT INTO evidence_references(analysis_id,file_id,ref_type,ref_value,note) VALUES(?,?,?,?,?)", (aid, fid, i["ref"]["type"], str(i["ref"]["value"])[:500], i["name"]), commit=True)
    return aid

def clean_err(e):
    return (type(e).__name__ + ": " + str(e)).replace(str(BASE), "")[:250]

def run_job(job_id, fid):
    started = now()
    try:
        f = q("SELECT * FROM uploaded_files WHERE id=?", (fid,), one=True)
        q("UPDATE uploaded_files SET status='analyzing' WHERE id=?", (fid,), commit=True)
        audit(f["investigation_id"], "analysis_started", f"{f['kind']} file={fid}")
        ctx = {}
        if f["kind"] == "text":   # reuse audio transcript from the same investigation, if any
            for it in latest_results(f["investigation_id"]):
                if it["kind"] == "audio" and (it["result"].get("transcript") or {}).get("text"): ctx["transcript"] = it["result"]["transcript"]["text"]
        r = ANALYZERS[f["kind"]](UPLOADS / f["stored_name"], ctx)   # originals are only read, never modified
        aid = save_result(fid, r, started)
        q("UPDATE uploaded_files SET status='complete' WHERE id=?", (fid,), commit=True)
        audit(f["investigation_id"], "analysis_completed", f"{f['kind']} label={r['label']} method={r['method']}")
        JOBS[job_id].update(status="done", result=r, analysis_id=aid)
    except Exception as e:
        log.error("job failed: %s", traceback.format_exc())
        q("UPDATE uploaded_files SET status='failed' WHERE id=?", (fid,), commit=True)
        JOBS[job_id].update(status="error", error=clean_err(e))

def inv_data(inv_id):
    inv = q("SELECT * FROM investigations WHERE id=?", (inv_id,), one=True)
    if not inv: return None
    files = q("SELECT id,original_name,kind,ext,size,sha256,uploaded_at,status FROM uploaded_files WHERE investigation_id=? ORDER BY uploaded_at", (inv_id,))
    res = {r["fid"]: r for r in latest_results(inv_id)}
    for f in files: f["result"] = res[f["id"]]["result"] if f["id"] in res else None
    return {**inv, "files": files, "audit": q("SELECT event,detail,ts FROM audit_logs WHERE investigation_id=? ORDER BY id", (inv_id,)),
            "correlation": q("SELECT relation,status,explanation,sources_json FROM cross_modal_findings WHERE investigation_id=?", (inv_id,))}

# 11. PDF / JSON REPORTS
def build_reports(inv_id):
    from xml.sax.saxutils import escape as E
    from reportlab.lib.pagesizes import A4
    from reportlab.lib import colors
    from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
    from reportlab.lib.units import mm
    from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak
    corr = correlate(inv_id); data = inv_data(inv_id)
    st = getSampleStyleSheet(); sm = ParagraphStyle("sm", parent=st["BodyText"], fontSize=8, leading=10)
    h1 = ParagraphStyle("h1", parent=st["Heading1"], textColor=colors.HexColor("#0b1f3a")); h2 = ParagraphStyle("h2", parent=st["Heading2"], textColor=colors.HexColor("#0a6ea8"))
    P = lambda t, s=sm: Paragraph(E(str(t)), s)
    def tbl(rows, widths=None, head=True):
        t = Table([[P(c) for c in r] for r in rows], colWidths=widths, repeatRows=1 if head else 0)
        t.setStyle(TableStyle([("GRID", (0, 0), (-1, -1), .4, colors.grey), ("VALIGN", (0, 0), (-1, -1), "TOP")] + ([("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#d8ecf7"))] if head else [])))
        return t
    S = []
    S += [Paragraph("Veridex Forensic Report", h1), P("Multimodal Digital Forensics & Deepfake Detection - INNOVEDGE HACKATHON 2026 (PS-04)", st["BodyText"]),
          tbl([["Investigation ID", data["id"]], ["Title", data["title"]], ["Report generated (UTC)", now()], ["Files analysed", len(data["files"])], ["Tool version", "Veridex " + APP_VERSION]], [45 * mm, 125 * mm], head=False), Spacer(1, 6)]
    S.append(Paragraph("1. Evidence Files", h2))
    S.append(tbl([["File name", "Type", "Size (bytes)", "SHA-256", "Uploaded (UTC)"]] + [[f["original_name"], f["kind"] + "/" + f["ext"], f["size"], f["sha256"], f["uploaded_at"]] for f in data["files"]], [32 * mm, 20 * mm, 20 * mm, 68 * mm, 30 * mm]))
    titles = {"image": "Image Analysis Results", "video": "Video Analysis Results", "audio": "Audio Analysis Results", "text": "Text Analysis Results"}
    n = 2
    for kind, title in titles.items():
        S.append(Paragraph(f"{n}. {title}", h2)); n += 1
        fs = [f for f in data["files"] if f["kind"] == kind and f["result"]]
        if not fs: S.append(P(f"No {kind} evidence was analysed in this investigation.")); continue
        for f in fs:
            r = f["result"]
            S.append(tbl([["File", f["original_name"]], ["Finding", r["label"]], ["Detection method", r["method"]], ["Model", f"{r['model']['name']} ({r['model']['version']}) - {r['model']['type']}"],
                          ["Score", (str(r["score"]["value"]) + " - " if r["score"]["value"] is not None else "") + r["score"]["type"]], ["Explanation", r["explanation"]], ["Uncertainty", r["uncertainty"]], ["Analysed (UTC)", r["analyzed_at"]]], [35 * mm, 135 * mm], head=False))
            if r["indicators"]: S.append(tbl([["Indicator", "Severity", "Timestamp", "Description"]] + [[i["name"], i["severity"], i.get("timestamp") if i.get("timestamp") is not None else "-", i["description"]] for i in r["indicators"]], [38 * mm, 16 * mm, 18 * mm, 98 * mm]))
            S.append(Spacer(1, 5))
    S.append(Paragraph(f"{n}. Cross-Modal Correlation", h2)); n += 1
    S.append(tbl([["Relation", "Status", "Explanation", "Sources"]] + [[r["relation"], r["status"], r["explanation"], ", ".join(r["sources"])] for r in corr["relations"]], [35 * mm, 22 * mm, 80 * mm, 33 * mm]))
    S.append(P(corr["note"]))
    S.append(Paragraph(f"{n}. Flagged Evidence, Suspicious Timestamps / Regions & Evidence References", h2)); n += 1
    refs = q("""SELECT f.original_name n,e.ref_type t,e.ref_value v,e.note FROM evidence_references e JOIN uploaded_files f ON f.id=e.file_id WHERE f.investigation_id=?""", (inv_id,))
    S.append(tbl([["File", "Reference type", "Reference", "Related indicator"]] + [[r["n"], r["t"], r["v"], r["note"]] for r in refs], [38 * mm, 25 * mm, 70 * mm, 37 * mm]) if refs else P("No evidence references were recorded."))
    S.append(Paragraph(f"{n}. Confidence and Uncertainty", h2)); n += 1
    S.append(P("Heuristic checks produce NO probability. Scores shown (if any) come from pretrained models and are UNCALIBRATED. Scores of different files/models are never merged into one overall percentage. 'No indicators' does not guarantee authenticity; indicators do not prove manipulation."))
    S.append(Paragraph(f"{n}. Analysis Limitations", h2)); n += 1
    lim = sorted({l for f in data["files"] if f["result"] for l in f["result"]["limitations"]})
    S += [P("- " + l) for l in lim] or [P("None recorded.")]
    S.append(P("- Evidence tracking (SHA-256, timestamps, audit log) supports traceability but is NOT a legally certified chain of custody."))
    S.append(Paragraph(f"{n}. Final Summary", h2)); n += 1
    S.append(P("; ".join(f"{f['original_name']}: {f['result']['label']}" for f in data["files"] if f["result"]) or "No completed analyses."))
    S.append(Paragraph(f"{n}. Recommended Human Verification", h2))
    S += [P("- Review every flagged region/frame/segment manually and compare with the original source."), P("- Seek the original device/file, contact the claimed author, and check provenance (e.g. C2PA credentials)."), P("- Use additional independent tools and a qualified forensic examiner before drawing conclusions.")]
    S.append(Paragraph("Audit Trail", h2)); S.append(tbl([["Time (UTC)", "Event", "Detail"]] + [[a["ts"], a["event"], a["detail"]] for a in data["audit"]], [38 * mm, 35 * mm, 97 * mm]))
    pdf, js = f"Veridex_{inv_id}.pdf", f"Veridex_{inv_id}.json"
    SimpleDocTemplate(str(REPORTS / pdf), pagesize=A4, leftMargin=18 * mm, rightMargin=18 * mm, topMargin=15 * mm, bottomMargin=15 * mm, title="Veridex Report " + inv_id).build(S)
    export = json.loads(json.dumps({"investigation": data, "correlation": corr}, default=str))
    for f in export["investigation"]["files"]:   # keep JSON export light: drop bulky base64 images
        for k in ("heatmap", "spectrogram", "waveform", "timeline"):
            if f["result"]: f["result"].pop(k, None)
        for fr in (f["result"] or {}).get("frames_flagged", []): fr.pop("thumb", None)
    (REPORTS / js).write_text(json.dumps(export, indent=2), encoding="utf-8")
    q("INSERT INTO forensic_reports(investigation_id,pdf_name,json_name,created_at) VALUES(?,?,?,?)", (inv_id, pdf, js, now()), commit=True)
    audit(inv_id, "report_generated", pdf)
    return pdf, js

# 12. FLASK API

app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = MAX_UPLOAD

def err(msg, code=400): return jsonify({"error": msg}), code

@app.errorhandler(413)
def too_big(e): return err(f"File too large (limit {MAX_UPLOAD // 1048576} MB).", 413)
@app.errorhandler(404)
def nf(e): return err("Not found.", 404)
@app.errorhandler(500)
def ise(e): return err("Internal server error.", 500)

@app.after_request
def sec(resp):
    resp.headers["X-Content-Type-Options"] = "nosniff"; resp.headers["X-Frame-Options"] = "DENY"; resp.headers["Referrer-Policy"] = "no-referrer"
    return resp

def valid_id(x): return bool(x) and ID_RE.match(str(x)) is not None

@app.get("/api/health")
def health():
    return jsonify({"status": "ok", "version": APP_VERSION, "components": {"opencv": HAS_CV2, "soundfile": HAS_SF, "librosa": HAS_LIBROSA, "ffmpeg": ffmpeg_ok(),
                    "transformers": bool(__import__("importlib").util.find_spec("transformers")), "whisper": bool(__import__("importlib").util.find_spec("whisper"))}})

@app.post("/api/investigations")
def new_inv():
    j = request.get_json(silent=True) or {}; iid = "INV-" + uuid.uuid4().hex[:10].upper()
    q("INSERT INTO investigations(id,title,created_at) VALUES(?,?,?)", (iid, str(j.get("title") or "Untitled investigation")[:120], now()), commit=True)
    audit(iid, "investigation_created", ""); return jsonify({"id": iid}), 201

@app.post("/api/upload")
def upload():
    f = request.files.get("file"); inv = request.form.get("investigation_id", ""); want = request.form.get("kind", "")
    if not f or not f.filename: return err("No file provided.")
    if not valid_id(inv) or not q("SELECT 1 x FROM investigations WHERE id=?", (inv,), one=True): return err("Unknown investigation.", 404)
    orig = secure_filename(f.filename) or "file"; ext = orig.rsplit(".", 1)[-1].lower() if "." in orig else ""
    kind = kind_of(ext)
    if not kind: return err(f"Unsupported file type '.{ext}'. Allowed: " + ", ".join(sorted(e for s in EXT.values() for e in s)), 415)
    if want and want != kind: return err(f"This page accepts {want} files, but '.{ext}' is a {kind} file.", 415)
    stored = uuid.uuid4().hex + "." + ext; dest = UPLOADS / stored; h = hashlib.sha256(); size = 0
    with open(dest, "wb") as out:   # stream to disk + hash the ORIGINAL bytes
        for ch in iter(lambda: f.stream.read(1 << 20), b""): h.update(ch); out.write(ch); size += len(ch)
    if size == 0 or not validate_content(dest, ext, kind):
        dest.unlink(missing_ok=True); return err("File content does not match its extension or is empty/corrupt.", 415)
    os.chmod(dest, 0o444)   # preserve original evidence read-only
    fid = "F" + uuid.uuid4().hex[:12]
    q("INSERT INTO uploaded_files(id,investigation_id,original_name,stored_name,kind,ext,size,sha256,uploaded_at) VALUES(?,?,?,?,?,?,?,?,?)", (fid, inv, orig, stored, kind, ext, size, h.hexdigest(), now()), commit=True)
    audit(inv, "file_uploaded", f"{orig} kind={kind} size={size} sha256={h.hexdigest()}")
    return jsonify({"file_id": fid, "name": orig, "kind": kind, "size": size, "sha256": h.hexdigest()}), 201

def start(kind):
    j = request.get_json(silent=True) or {}; fid = j.get("file_id")
    if not valid_id(fid): return err("file_id required.")
    f = q("SELECT kind FROM uploaded_files WHERE id=?", (fid,), one=True)
    if not f: return err("Unknown file.", 404)
    if f["kind"] != kind: return err(f"File is a {f['kind']} file, not {kind}.", 400)
    jid = uuid.uuid4().hex[:12]; JOBS[jid] = {"status": "running", "file_id": fid}
    threading.Thread(target=run_job, args=(jid, fid), daemon=True).start()
    return jsonify({"job_id": jid}), 202

for _k in EXT:   # POST /api/analyze/<image|video|audio|text>
    app.add_url_rule(f"/api/analyze/{_k}", f"an_{_k}", (lambda k: lambda: start(k))(_k), methods=["POST"])

@app.get("/api/jobs/<jid>")
def job(jid):
    j = JOBS.get(jid)
    return jsonify(j) if j else err("Unknown job.", 404)

@app.post("/api/correlate")
def corr_route():
    iid = (request.get_json(silent=True) or {}).get("investigation_id")
    if not valid_id(iid) or not q("SELECT 1 x FROM investigations WHERE id=?", (iid,), one=True): return err("Unknown investigation.", 404)
    return jsonify(correlate(iid))

@app.get("/api/investigations")
def list_inv():
    return jsonify(q("""SELECT i.id,i.title,i.created_at,i.status,(SELECT COUNT(*) FROM uploaded_files WHERE investigation_id=i.id) files,
      (SELECT COUNT(*) FROM analysis_results r JOIN uploaded_files f ON f.id=r.file_id WHERE f.investigation_id=i.id AND r.label='Potential manipulation detected') flagged
      FROM investigations i ORDER BY i.created_at DESC"""))

@app.get("/api/investigations/<iid>")
def get_inv(iid):
    d = inv_data(iid) if valid_id(iid) else None
    return jsonify(d) if d else err("Unknown investigation.", 404)

@app.delete("/api/investigations/<iid>")
def del_inv(iid):
    """User-initiated deletion (retention: evidence stays on disk until the user deletes the investigation)."""
    if not valid_id(iid) or not q("SELECT 1 x FROM investigations WHERE id=?", (iid,), one=True): return err("Unknown investigation.", 404)
    for f in q("SELECT stored_name FROM uploaded_files WHERE investigation_id=?", (iid,)):
        try: os.chmod(UPLOADS / f["stored_name"], 0o644); (UPLOADS / f["stored_name"]).unlink(missing_ok=True)
        except OSError: pass
    for r in q("SELECT pdf_name,json_name FROM forensic_reports WHERE investigation_id=?", (iid,)):
        for n in (r["pdf_name"], r["json_name"]): (REPORTS / n).unlink(missing_ok=True)
    q("DELETE FROM investigations WHERE id=?", (iid,), commit=True); audit(None, "investigation_deleted", iid)
    return jsonify({"deleted": iid})

@app.get("/api/file/<fid>")
def raw_file(fid):
    f = q("SELECT stored_name,ext FROM uploaded_files WHERE id=?", (fid,), one=True) if valid_id(fid) else None
    if not f: return err("Unknown file.", 404)
    return send_file(UPLOADS / f["stored_name"], mimetype=MIME[f["ext"]], conditional=True)

@app.get("/api/reports/<iid>")
def report(iid):
    if not valid_id(iid) or not q("SELECT 1 x FROM investigations WHERE id=?", (iid,), one=True): return err("Unknown investigation.", 404)
    try: pdf, js = build_reports(iid)
    except Exception as e: log.error(traceback.format_exc()); return err("Report generation failed: " + clean_err(e), 500)
    return jsonify({"investigation_id": iid, "pdf": f"/api/reports/{iid}/download?format=pdf", "json": f"/api/reports/{iid}/download?format=json", "data": json.loads((REPORTS / js).read_text("utf-8"))})

@app.get("/api/reports/<iid>/download")
def report_dl(iid):
    fmt = request.args.get("format", "pdf")
    if not valid_id(iid) or fmt not in ("pdf", "json"): return err("Bad request.")
    r = q("SELECT pdf_name,json_name FROM forensic_reports WHERE investigation_id=? ORDER BY id DESC", (iid,), one=True)
    if not r:
        if not q("SELECT 1 x FROM investigations WHERE id=?", (iid,), one=True): return err("Unknown investigation.", 404)
        build_reports(iid); r = q("SELECT pdf_name,json_name FROM forensic_reports WHERE investigation_id=? ORDER BY id DESC", (iid,), one=True)
    else: build_reports(iid); r = q("SELECT pdf_name,json_name FROM forensic_reports WHERE investigation_id=? ORDER BY id DESC", (iid,), one=True)
    n = r["pdf_name"] if fmt == "pdf" else r["json_name"]
    return send_file(REPORTS / n, as_attachment=True, download_name=n, mimetype="application/pdf" if fmt == "pdf" else "application/json")

@app.get("/api/dashboard/stats")
def stats():
    sc = lambda sql, a=(): q(sql, a, one=True)["c"]
    kinds = {k: sc("SELECT COUNT(*) c FROM analysis_results WHERE kind=?", (k,)) for k in EXT}
    outcomes = {r["label"]: r["c"] for r in q("SELECT label,COUNT(*) c FROM analysis_results GROUP BY label")}
    return jsonify({"investigations": sc("SELECT COUNT(*) c FROM investigations"), "files": sc("SELECT COUNT(*) c FROM uploaded_files"), "analyzed": kinds,
                    "suspicious": outcomes.get(LABELS[1], 0), "inconclusive": outcomes.get(LABELS[2], 0), "outcomes": outcomes,
                    "history": q("SELECT substr(created_at,1,10) d,COUNT(*) c FROM investigations GROUP BY d ORDER BY d DESC LIMIT 14")[::-1],
                    "activity": q("SELECT substr(completed_at,1,10) d,COUNT(*) c FROM analysis_results GROUP BY d ORDER BY d DESC LIMIT 14")[::-1],
                    "recent": q("SELECT id,title,created_at FROM investigations ORDER BY created_at DESC LIMIT 6")})

@app.get("/")
def index(): return Response(INDEX_HTML, mimetype="text/html")

# 13. FRONTEND (single-page app: hash routes #/dashboard #/image #/video ...)

INDEX_HTML = r'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Veridex - Multimodal Digital Forensics</title>
<script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.1/dist/chart.umd.min.js"></script>
<style>
:root{--bg:#050b18;--card:#0c1a30;--card2:#10233f;--line:#1c3558;--tx:#e8f1ff;--mut:#8aa4c8;--blue:#2f80ff;--cy:#22d3ee;--ok:#22c55e;--warn:#f59e0b;--bad:#ef4444}
*{box-sizing:border-box}body{margin:0;background:radial-gradient(circle at 20% -10%,#0d2a52 0,var(--bg) 45%);color:var(--tx);font:15px/1.55 "Segoe UI",system-ui,sans-serif;min-height:100vh}
a{color:var(--cy);text-decoration:none}
nav{position:sticky;top:0;z-index:20;background:#050b18ee;backdrop-filter:blur(8px);border-bottom:1px solid var(--line);display:flex;flex-wrap:wrap;align-items:center;gap:4px;padding:8px 18px}
nav .logo{font-weight:800;font-size:20px;margin-right:14px;background:linear-gradient(90deg,var(--blue),var(--cy));-webkit-background-clip:text;color:transparent}
nav a.l{padding:6px 11px;border-radius:8px;color:var(--mut);font-size:13.5px;transition:.2s}nav a.l:hover,nav a.l.on{background:var(--card2);color:var(--tx)}
#bar{margin-left:auto;font-size:12.5px;color:var(--mut);display:flex;gap:8px;align-items:center}
main{max-width:1180px;margin:0 auto;padding:24px 18px 60px;animation:fade .35s}@keyframes fade{from{opacity:0;transform:translateY(6px)}to{opacity:1}}
h1,h2,h3{margin:.2em 0 .5em}.muted{color:var(--mut)}.grid{display:grid;gap:14px}.g2{grid-template-columns:repeat(auto-fit,minmax(340px,1fr))}.g4{grid-template-columns:repeat(auto-fit,minmax(170px,1fr))}
.card{background:linear-gradient(180deg,var(--card),var(--card2));border:1px solid var(--line);border-radius:14px;padding:16px;margin-bottom:14px}
.stat b{font-size:30px;display:block;color:var(--cy)}
button,.btn{background:linear-gradient(90deg,var(--blue),#1d9bd6);color:#fff;border:0;border-radius:9px;padding:9px 16px;cursor:pointer;font-weight:600;font-size:14px;transition:.2s}button:hover{filter:brightness(1.15);transform:translateY(-1px)}
button.sec{background:var(--card2);border:1px solid var(--line)}button.del{background:#7f1d1d}button:disabled{opacity:.5;cursor:wait}
input[type=file],textarea,select{width:100%;background:#071226;color:var(--tx);border:1px dashed var(--line);border-radius:9px;padding:10px}textarea{min-height:150px;border-style:solid;font-family:inherit}
table{width:100%;border-collapse:collapse;font-size:13.5px}th,td{padding:7px 9px;border-bottom:1px solid var(--line);text-align:left;vertical-align:top}th{color:var(--mut);font-weight:600}
.badge{display:inline-block;padding:3px 11px;border-radius:999px;font-weight:700;font-size:13px}
.b0{background:#0f3b24;color:#6ee7a0}.b1{background:#5b1a1a;color:#fca5a5}.b2{background:#4a3507;color:#fcd34d}.b3,.b4{background:#243247;color:#b6c6de}
.sev-high{color:var(--bad)}.sev-medium{color:var(--warn)}.sev-low{color:var(--cy)}.sev-info{color:var(--mut)}
.hero{padding:60px 10px;text-align:center}.hero h1{font-size:50px;margin:0;background:linear-gradient(90deg,#fff,var(--cy),var(--blue));-webkit-background-clip:text;color:transparent}
img.pv,video.pv{max-width:100%;max-height:360px;border-radius:10px;border:1px solid var(--line)}audio{width:100%}
.frames{display:grid;grid-template-columns:repeat(auto-fill,minmax(180px,1fr));gap:10px}.frames img{width:100%;border-radius:8px;cursor:pointer;border:2px solid var(--warn)}
#modal{position:fixed;inset:0;background:#000c;display:none;align-items:center;justify-content:center;z-index:50;padding:20px}#modal .card{max-width:720px;max-height:90vh;overflow:auto}
.chip{display:inline-block;padding:2px 9px;border-radius:6px;font-size:12px;font-weight:700}.c-supporting{background:#0f3b24;color:#6ee7a0}.c-contradictory{background:#5b1a1a;color:#fca5a5}.c-insufficient,.c-neutral{background:#243247;color:#b6c6de}
mark{background:#f59e0b44;color:#fff;padding:1px 3px;border-radius:3px}.note{border-left:3px solid var(--warn);padding:6px 12px;background:#f59e0b12;margin:8px 0;font-size:13.5px}
.spin{display:inline-block;width:14px;height:14px;border:2px solid var(--line);border-top-color:var(--cy);border-radius:50%;animation:sp 1s linear infinite;vertical-align:middle;margin-right:6px}@keyframes sp{to{transform:rotate(360deg)}}
canvas{max-height:260px}ul{margin:.3em 0;padding-left:20px}
</style></head><body>
<nav><span class="logo">&#9673; Veridex</span>
<a class="l" href="#/">Home</a><a class="l" href="#/dashboard">Dashboard</a><a class="l" href="#/image">Image</a><a class="l" href="#/video">Video</a><a class="l" href="#/audio">Audio</a><a class="l" href="#/text">Text</a><a class="l" href="#/correlation">Correlation</a><a class="l" href="#/history">History</a><a class="l" href="#/reports">Reports</a><a class="l" href="#/about">About</a>
<div id="bar"></div></nav><main id="view"></main>
<div id="modal" onclick="if(event.target===this)this.style.display='none'"><div class="card" id="mbody"></div></div>
<script>
const $=s=>document.querySelector(s), esc=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
async function api(p,o={}){const r=await fetch('/api'+p,o);let j={};try{j=await r.json()}catch(e){}if(!r.ok)throw new Error(j.error||('HTTP '+r.status));return j}
const jpost=(p,b)=>api(p,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(b)});
let INV=localStorage.getItem('vx_inv')||'', charts=[];
function setInv(id){INV=id;localStorage.setItem('vx_inv',id);bar()}
function bar(){$('#bar').innerHTML=(INV?`Investigation <b style="color:var(--cy)">${esc(INV)}</b>`:'No active investigation')+` <button class="sec" onclick="newInv()">+ New</button>`}
async function newInv(){const j=await jpost('/investigations',{title:'Investigation '+new Date().toLocaleString()});setInv(j.id);if(location.hash.length>2)route()}
async function ensureInv(){if(INV){try{await api('/investigations/'+INV);return INV}catch(e){}}await newInv();return INV}
const badge=l=>{const i=['No significant indicators detected','Potential manipulation detected','Inconclusive','Insufficient evidence','Analysis unavailable'].indexOf(l);return `<span class="badge b${i<0?3:i}">${esc(l)}</span>`};
function chart(id,type,labels,data,label,colors){if(typeof Chart==='undefined'){const e=document.getElementById(id);if(e)e.outerHTML='<p class="muted">Charts need internet access for Chart.js (CDN). Data: '+esc(JSON.stringify(labels.map((l,i)=>l+': '+data[i])))+'</p>';return}
 const c=new Chart(document.getElementById(id),{type,data:{labels,datasets:[{label,data,backgroundColor:colors||['#2f80ff','#22d3ee','#8b5cf6','#f59e0b','#ef4444','#22c55e'],borderColor:'#22d3ee',tension:.3,fill:type==='line'}]},options:{plugins:{legend:{labels:{color:'#cfe0ff'}}},scales:type==='doughnut'?{}:{x:{ticks:{color:'#8aa4c8'}},y:{ticks:{color:'#8aa4c8'},beginAtZero:true}}}});charts.push(c)}
function modal(h){$('#mbody').innerHTML=h+'<p><button class="sec" onclick="$(\'#modal\').style.display=\'none\'">Close</button></p>';$('#modal').style.display='flex'}

const PAGES={};
PAGES['/']=()=>`<div class="hero"><h1>Veridex</h1><p style="font-size:20px" class="muted">Multimodal Digital Forensics &amp; Deepfake Detection System</p>
<p>Analyse image, video, audio and text evidence, correlate findings across media, and get explainable, uncertainty-aware forensic reports.</p>
<a class="btn" href="#/image">Start analysis</a> <a class="btn" style="background:var(--card2)" href="#/dashboard">Open dashboard</a></div>
<div class="grid g4">${[['Image','ELA, metadata, AI-generator markers, optional pretrained detector','#/image'],['Video','Frame extraction, temporal consistency, face statistics, timeline','#/video'],['Audio','Waveform, spectrogram, splice/continuity checks, transcript','#/audio'],['Text','Claim wording, internal & transcript contradictions','#/text'],['Correlation','Supporting vs contradictory evidence across files','#/correlation'],['Reports','PDF + JSON with SHA-256 &amp; audit trail','#/reports']].map(x=>`<a href="${x[2]}" class="card"><h3>${x[0]}</h3><span class="muted">${x[1]}</span></a>`).join('')}</div>
<div class="note">Veridex reports <b>indicators</b>, never proof. No detected indicators does not guarantee authenticity.</div>`;

PAGES['/dashboard']=async()=>{const s=await api('/dashboard/stats');setTimeout(()=>{chart('c1','doughnut',Object.keys(s.analyzed),Object.values(s.analyzed),'Media');chart('c2','line',s.history.map(x=>x.d),s.history.map(x=>x.c),'Investigations');chart('c3','bar',Object.keys(s.outcomes),Object.values(s.outcomes),'Outcomes');chart('c4','bar',s.activity.map(x=>x.d),s.activity.map(x=>x.c),'Analyses')},50);
return `<h2>Dashboard</h2><p class="muted">All figures are computed from stored database records.</p><div class="grid g4">${[['Investigations',s.investigations],['Files analysed',s.files],['Images',s.analyzed.image],['Videos',s.analyzed.video],['Audio',s.analyzed.audio],['Text',s.analyzed.text],['Potentially suspicious',s.suspicious],['Inconclusive',s.inconclusive]].map(x=>`<div class="card stat"><span class="muted">${x[0]}</span><b>${x[1]}</b></div>`).join('')}</div>
<div class="grid g2"><div class="card"><h3>Media type distribution</h3><canvas id="c1"></canvas></div><div class="card"><h3>Investigation history</h3><canvas id="c2"></canvas></div><div class="card"><h3>Detection outcomes</h3><canvas id="c3"></canvas></div><div class="card"><h3>Analysis activity</h3><canvas id="c4"></canvas></div></div>
<div class="card"><h3>Recent investigations</h3>${s.recent.length?`<table><tr><th>ID</th><th>Title</th><th>Created</th><th></th></tr>${s.recent.map(r=>`<tr><td>${r.id}</td><td>${esc(r.title)}</td><td>${r.created_at}</td><td><button class="sec" onclick="openInv('${r.id}')">Open</button></td></tr>`).join('')}</table>`:'<p class="muted">No investigations yet.</p>'}</div>`};

function analysisPage(kind,accept,title,desc){return()=>`<h2>${title}</h2><p class="muted">${desc}</p><div class="card">
${kind==='text'?'<textarea id="txt" placeholder="Paste a caption, description or transcript here..."></textarea><p class="muted">or upload a .txt file:</p>':''}
<input type="file" id="f" accept="${accept}"><p><button id="go" onclick="runAnalysis('${kind}')">Upload &amp; Analyze</button> <span id="st" class="muted"></span></p><div id="pv"></div></div><div id="res"></div>`}
PAGES['/image']=analysisPage('image','.jpg,.jpeg,.png,.webp','Image Authenticity Analysis','JPG, JPEG, PNG, WEBP. Metadata, error-level analysis and (if installed) a pretrained AI-image detector.');
PAGES['/video']=analysisPage('video','.mp4,.avi,.mov,.mkv','Video Forensics','MP4, AVI, MOV, MKV. Frames are extracted with OpenCV (FFmpeg fallback) and checked for visual/temporal consistency.');
PAGES['/audio']=analysisPage('audio','.wav,.mp3,.m4a,.flac','Audio &amp; Voice Analysis','WAV, MP3, M4A, FLAC. Waveform, spectrogram, spectral/continuity checks, optional transcript.');
PAGES['/text']=analysisPage('text','.txt','Text &amp; Context Analysis','Plain text or .txt upload. Compared automatically with the audio transcript in the active investigation when available.');

async function runAnalysis(kind){const st=$('#st'),go=$('#go');let file=$('#f').files[0];
 if(kind==='text'&&$('#txt').value.trim()){file=new File([$('#txt').value],'pasted_text.txt',{type:'text/plain'})}
 if(!file){st.textContent='Choose a file first.';return}
 go.disabled=true;$('#res').innerHTML='';
 try{const inv=await ensureInv();st.innerHTML='<span class="spin"></span>Uploading and hashing...';
  const fd=new FormData();fd.append('file',file);fd.append('investigation_id',inv);fd.append('kind',kind);
  const up=await api('/upload',{method:'POST',body:fd});
  const url='/api/file/'+up.file_id;
  $('#pv').innerHTML=kind==='image'?`<img class="pv" src="${url}">`:kind==='video'?`<video class="pv" controls src="${url}"></video>`:kind==='audio'?`<audio id="aud" controls src="${url}"></audio>`:'';
  $('#pv').innerHTML+=`<p class="muted">SHA-256: <code>${up.sha256}</code> &middot; ${up.size} bytes (original preserved read-only)</p>`;
  st.innerHTML='<span class="spin"></span>Analyzing...';const {job_id}=await jpost('/analyze/'+kind,{file_id:up.file_id});
  for(;;){await new Promise(r=>setTimeout(r,900));const j=await api('/jobs/'+job_id);if(j.status==='done'){render(j.result,kind);break}if(j.status==='error')throw new Error(j.error)}
  st.textContent='Done.'}catch(e){st.textContent='';$('#res').innerHTML=`<div class="card" style="border-color:var(--bad)"><b>Error:</b> ${esc(e.message)}</div>`}go.disabled=false}

function render(r,kind){charts.forEach(c=>c.destroy());charts=[];let h=`<div class="card"><h3>Detection result</h3><p>${badge(r.label)}</p><p>${esc(r.explanation)}</p>
<table><tr><th>Detection method</th><td>${esc(r.method)}</td></tr><tr><th>Model</th><td>${esc(r.model.name)} <span class="muted">(${esc(r.model.version)}) - ${esc(r.model.type)}</span></td></tr>
<tr><th>Score</th><td>${r.score.value!==null?`<b>${r.score.value}</b> - `:''}${esc(r.score.type)}</td></tr><tr><th>Uncertainty</th><td>${esc(r.uncertainty)}</td></tr></table></div>`;
 if(r.indicators.length)h+=`<div class="card"><h3>Detected indicators &amp; evidence references</h3><table><tr><th>Severity</th><th>Indicator</th><th>Time</th><th>Explanation</th><th>Evidence reference</th></tr>${r.indicators.map(i=>`<tr><td class="sev-${i.severity}"><b>${i.severity}</b></td><td>${esc(i.name)}</td><td>${i.timestamp!=null?`<a href="#" onclick="seek(${i.timestamp});return false">${i.timestamp}s</a>`:'-'}</td><td>${esc(i.description)}</td><td>${i.ref?esc(i.ref.type+': '+i.ref.value):'-'}</td></tr>`).join('')}</table></div>`;
 if(kind==='image'){h+=`<div class="grid g2"><div class="card"><h3>Suspicious-region heatmap (ELA)</h3>${r.heatmap?`<img class="pv" src="${r.heatmap}"><p class="muted">Red = higher recompression error; cyan boxes = top regions. Heuristic visualisation.</p>`:'<p class="muted">Unavailable</p>'}</div><div class="card"><h3>Metadata</h3><table>${Object.entries(r.metadata).filter(([k,v])=>typeof v!=='object').map(([k,v])=>`<tr><th>${k}</th><td>${esc(v)}</td></tr>`).join('')}${Object.entries(r.metadata.exif||{}).slice(0,25).map(([k,v])=>`<tr><th>EXIF ${esc(k)}</th><td>${esc(v)}</td></tr>`).join('')||'<tr><td>No EXIF</td></tr>'}</table>${r.model_output?'<h3>Model output</h3>'+r.model_output.map(m=>esc(m.label)+': '+m.score).join('<br>'):''}</div></div>`}
 if(kind==='video'){const m=r.metadata;h+=`<div class="card"><h3>Video timeline</h3><p class="muted">${esc(r.frame_summary||'')} &middot; ${m.duration_sec}s, ${m.fps} fps, ${m.width}x${m.height}, codec ${esc(m.codec)}</p><canvas id="tl"></canvas></div>
 <div class="card"><h3>Flagged frames (click to inspect)</h3>${r.frames_flagged.length?`<div class="frames">${r.frames_flagged.map((f,i)=>`<div><img src="${f.thumb}" onclick="frameModal(${i})"><small>#${f.frame} @ ${f.time}s<br>${esc(f.indicators.join(', '))}</small></div>`).join('')}</div>`:'<p class="muted">No frames flagged.</p>'}</div>`;window._frames=r.frames_flagged;
 setTimeout(()=>{if(typeof Chart==='undefined')return;const c=new Chart($('#tl'),{type:'line',data:{labels:r.timeline.map(x=>x.t+'s'),datasets:[{label:'Visual change vs previous sampled frame',data:r.timeline.map(x=>x.diff),borderColor:'#22d3ee',pointBackgroundColor:r.timeline.map(x=>x.flag?'#ef4444':'#22d3ee'),pointRadius:r.timeline.map(x=>x.flag?6:2)}]},options:{plugins:{legend:{labels:{color:'#cfe0ff'}}},scales:{x:{ticks:{color:'#8aa4c8'}},y:{ticks:{color:'#8aa4c8'}}}}});charts.push(c)},50)}
 if(kind==='audio'){h+=`<div class="card"><h3>Waveform</h3><canvas id="wf"></canvas><h3>Spectrogram</h3><img class="pv" style="width:100%;max-height:none" src="${r.spectrogram}"><p class="muted">${esc((r.spectral_observations||[]).join(' '))}</p></div>
 <div class="card"><h3>Transcript</h3>${r.transcript?`<p>${esc(r.transcript.text)}</p><p class="muted">Engine: ${esc(r.transcript.engine)}</p>`:'<p class="muted">Unavailable - install openai-whisper for offline transcription.</p>'}<h3>Flagged timestamps</h3>${r.flagged.length?r.flagged.map(f=>`<a href="#" onclick="seek(${f.start});return false">${f.start}s</a> (${esc(f.reason)})`).join(' &middot; '):'<span class="muted">None</span>'}</div>`;
 setTimeout(()=>{if(typeof Chart==='undefined')return;const d=r.metadata.duration_sec/r.waveform.length;const c=new Chart($('#wf'),{type:'line',data:{labels:r.waveform.map((_,i)=>(i*d).toFixed(1)),datasets:[{label:'Peak amplitude',data:r.waveform,borderColor:'#2f80ff',backgroundColor:'#2f80ff55',fill:true,pointRadius:0,borderWidth:1}]},options:{plugins:{legend:{labels:{color:'#cfe0ff'}}},scales:{x:{ticks:{color:'#8aa4c8',maxTicksLimit:12}},y:{ticks:{color:'#8aa4c8'}}}}});charts.push(c)},50)}
 if(kind==='text'){h+=`<div class="card"><h3>Highlighted contradictions / suspicious claims</h3>${(r.highlights||[]).length?r.highlights.map(x=>`<p><mark>${esc(x.sentence)}</mark><br><span class="muted">${esc(x.reason)}</span></p>`).join(''):'<p class="muted">None highlighted.</p>'}<p class="muted">${esc(JSON.stringify(r.metadata))}</p></div>`}
 h+=`<div class="grid g2"><div class="card"><h3>Alternative explanations</h3><ul>${r.alternatives.map(a=>`<li>${esc(a)}</li>`).join('')}</ul></div><div class="card"><h3>Analysis limitations</h3><ul>${r.limitations.map(a=>`<li>${esc(a)}</li>`).join('')}</ul></div></div><div class="note">${esc(r.disclaimer)}</div>`;
 $('#res').innerHTML=h}
function frameModal(i){const f=window._frames[i];modal(`<h3>Frame #${f.frame} @ ${f.time}s</h3><img src="${f.thumb}" style="width:100%;border-radius:8px"><p><b>Indicators:</b> ${esc(f.indicators.join(', '))}</p><p>${esc(f.note)}</p><p class="muted">${esc(f.confidence)}</p>`)}
function seek(t){const a=$('#aud')||document.querySelector('video');if(a){a.currentTime=t;a.play()}}

PAGES['/correlation']=()=>`<h2>Cross-Modal Correlation</h2><p class="muted">Compares findings of all files in the active investigation (video/audio timing &amp; duration, transcript vs text, image metadata vs description, multi-source pattern). Upload files on the other pages first.</p><div class="card"><button onclick="runCorr()">Run correlation for ${esc(INV||'(no investigation)')}</button></div><div id="res"></div>`;
async function runCorr(){if(!INV){$('#res').innerHTML='<div class="note">Upload evidence first.</div>';return}try{const c=await jpost('/correlate',{investigation_id:INV});
 $('#res').innerHTML=`<div class="card"><h3>Summary</h3><span class="chip c-supporting">${c.summary.supporting} supporting</span> <span class="chip c-contradictory">${c.summary.contradictory} contradictory</span> <span class="chip c-insufficient">${c.summary.insufficient} insufficient</span><div class="note">${esc(c.note)}</div></div>
 <div class="card"><h3>Source files</h3><table><tr><th>File</th><th>Media</th><th>Detection finding</th><th>Indicators</th></tr>${c.sources.map(s=>`<tr><td>${esc(s.file)}</td><td>${s.kind}</td><td>${badge(s.finding)}</td><td>${esc(s.indicators.join(', ')||'-')}</td></tr>`).join('')}</table></div>
 <div class="card"><h3>Relationships &amp; evidence</h3><table><tr><th>Relation</th><th>Status</th><th>Explanation</th><th>Related files</th></tr>${c.relations.map(r=>`<tr><td>${esc(r.relation)}</td><td><span class="chip c-${r.status}">${r.status}</span></td><td>${esc(r.explanation)}</td><td>${esc(r.sources.join(' / '))}</td></tr>`).join('')}</table></div>`}catch(e){$('#res').innerHTML=`<div class="card">${esc(e.message)}</div>`}}

PAGES['/history']=async()=>{const l=await api('/investigations');return `<h2>Investigation History</h2><div class="card">${l.length?`<table><tr><th>ID</th><th>Title</th><th>Created (UTC)</th><th>Files</th><th>Flagged</th><th></th></tr>${l.map(r=>`<tr><td>${r.id}</td><td>${esc(r.title)}</td><td>${r.created_at}</td><td>${r.files}</td><td>${r.flagged}</td><td><button class="sec" onclick="openInv('${r.id}')">Open</button> <button class="sec" onclick="dl('${r.id}','pdf')">PDF</button> <button class="del" onclick="delInv('${r.id}')">Delete</button></td></tr>`).join('')}</table>`:'<p class="muted">No investigations yet.</p>'}</div><p class="muted">Retention: uploaded evidence is kept on this machine (uploads/ folder, read-only) until you delete the investigation.</p>`};
async function openInv(id){try{const d=await api('/investigations/'+id);setInv(id);modal(`<h3>${d.id} - ${esc(d.title)}</h3><table><tr><th>File</th><th>Type</th><th>SHA-256</th><th>Finding</th></tr>${d.files.map(f=>`<tr><td>${esc(f.original_name)}</td><td>${f.kind}</td><td style="word-break:break-all;font-size:11px">${f.sha256}</td><td>${f.result?badge(f.result.label):f.status}</td></tr>`).join('')}</table><h3>Audit trail</h3><div style="max-height:200px;overflow:auto;font-size:12px">${d.audit.map(a=>`${a.ts} - <b>${a.event}</b> ${esc(a.detail)}`).join('<br>')}</div><p><button onclick="dl('${id}','pdf')">Download PDF</button> <button class="sec" onclick="dl('${id}','json')">Download JSON</button></p>`)}catch(e){alert(e.message)}}
function dl(id,f){location.href=`/api/reports/${id}/download?format=${f}`}
async function delInv(id){if(!confirm('Delete this investigation and its evidence files permanently?'))return;await api('/investigations/'+id,{method:'DELETE'});if(INV===id)setInv('');route()}

PAGES['/reports']=async()=>{const l=await api('/investigations');return `<h2>Forensic Reports</h2><p class="muted">Reports are generated on demand from stored results (hashes, indicators, correlation, audit trail).</p><div class="card">${l.length?`<table><tr><th>Investigation</th><th>Files</th><th></th></tr>${l.map(r=>`<tr><td>${r.id}<br><span class="muted">${esc(r.title)}</span></td><td>${r.files}</td><td><button onclick="dl('${r.id}','pdf')">Download PDF</button> <button class="sec" onclick="dl('${r.id}','json')">JSON export</button> <button class="sec" onclick="openInv('${r.id}')">View</button></td></tr>`).join('')}</table>`:'<p class="muted">No investigations yet.</p>'}</div>`};

PAGES['/about']=async()=>{let h={};try{h=await api('/health')}catch(e){}const c=h.components||{};return `<h2>About &amp; Methodology</h2><div class="grid g2"><div class="card"><h3>What Veridex does</h3><ul><li><b>Image:</b> metadata (EXIF/XMP/C2PA markers), Error Level Analysis, optional pretrained AI-image detector.</li><li><b>Video:</b> OpenCV frame sampling, histogram discontinuities, face-region statistics.</li><li><b>Audio:</b> STFT spectral analysis, splice/silence/discontinuity checks, optional Whisper transcript and audio model.</li><li><b>Text:</b> sensational/unverifiable wording, numeric inconsistencies, transcript comparison.</li><li><b>Correlation:</b> timestamps, durations, transcript similarity, metadata years, multi-source agreement.</li></ul></div>
<div class="card"><h3>Honest limits</h3><ul><li>Heuristics are not ML predictions and carry no probability.</li><li>Pretrained scores are uncalibrated.</li><li>Lip-sync analysis is not implemented.</li><li>Not a legally certified chain of custody.</li><li>No indicators &ne; authentic. Indicators &ne; fake.</li></ul></div>
<div class="card"><h3>Installed components on this machine</h3><table>${Object.entries(c).map(([k,v])=>`<tr><td>${k}</td><td>${v?'&#9989; available':'&#10060; not installed (feature degrades gracefully)'}</td></tr>`).join('')}</table></div></div>`};

async function route(){charts.forEach(c=>c.destroy());charts=[];const p=(location.hash||'#/').slice(1);document.querySelectorAll('nav a.l').forEach(a=>a.classList.toggle('on',a.getAttribute('href')==='#'+p));
 $('#view').innerHTML='<p class="muted"><span class="spin"></span>Loading...</p>';try{$('#view').innerHTML=await (PAGES[p]||PAGES['/'])()}catch(e){$('#view').innerHTML=`<div class="card">Error: ${esc(e.message)}</div>`}}
addEventListener('hashchange',route);bar();route();
</script></body></html>'''

# 14. SELF TEST (python app.py --selftest) - generates synthetic evidence, uses Flask test client
def selftest():
    global DB_PATH
    import tempfile as tf
    DB_PATH = Path(tf.mkdtemp()) / "test.db"; init_db(); c = app.test_client(); res = []
    def chk(name, cond, extra=""): cond = bool(cond); res.append(cond); print(("PASS " if cond else "FAIL ") + name, extra)
    inv = c.post("/api/investigations", json={"title": "selftest"}).get_json()["id"]
    def up(data, name, kind): return c.post("/api/upload", data={"file": (io.BytesIO(data), name), "investigation_id": inv, "kind": kind}, content_type="multipart/form-data")
    def run(kind, fid):
        jid = c.post("/api/analyze/" + kind, json={"file_id": fid}).get_json()["job_id"]
        for _ in range(300):
            j = c.get("/api/jobs/" + jid).get_json()
            if j["status"] != "running": return j
            time.sleep(0.5)
    chk("health", c.get("/api/health").status_code == 200)
    # image: JPEG with a pasted noisy patch
    rng = np.random.default_rng(1); arr = (np.linspace(0, 255, 256 * 256).reshape(256, 256, 1) * np.ones((1, 1, 3))).astype(np.uint8)
    im = Image.fromarray(arr); b = io.BytesIO(); im.save(b, "JPEG", quality=70); im = Image.open(io.BytesIO(b.getvalue())).convert("RGB")
    patch = Image.fromarray(rng.integers(0, 255, (40, 40, 3), dtype=np.uint8)); im.paste(patch, (100, 100)); b = io.BytesIO(); im.save(b, "JPEG", quality=95)
    r = up(b.getvalue(), "test.jpg", "image"); chk("image upload", r.status_code == 201); fid = r.get_json()["file_id"]
    chk("sha256 correct", r.get_json()["sha256"] == hashlib.sha256(b.getvalue()).hexdigest())
    j = run("image", fid); chk("image analysis", j["status"] == "done", j.get("result", {}).get("label", j.get("error")))
    chk("image has heatmap+limitations", "heatmap" in j["result"] and j["result"]["limitations"])
    # invalid / unsupported / spoofed
    chk("unsupported ext rejected", up(b"x", "a.exe", "image").status_code == 415)
    chk("spoofed content rejected", up(b"not an image", "fake.png", "image").status_code == 415)
    chk("wrong page kind rejected", up(b.getvalue(), "a.jpg", "audio").status_code == 415)
    chk("unknown file 404", c.post("/api/analyze/image", json={"file_id": "F000000000000"}).status_code == 404)
    # audio: tone + splice with digital silence
    sr = 16000; t = np.arange(sr * 4) / sr; y = (0.4 * np.sin(2 * np.pi * 220 * t) + 0.01 * rng.standard_normal(len(t))); y[2 * sr:int(2.2 * sr)] = 0
    wb = io.BytesIO(); w = wave.open(wb, "wb"); w.setnchannels(1); w.setsampwidth(2); w.setframerate(sr); w.writeframes((y * 32767).astype("<i2").tobytes()); w.close()
    r = up(wb.getvalue(), "tone.wav", "audio"); chk("audio upload", r.status_code == 201); j = run("audio", r.get_json()["file_id"])
    chk("audio analysis", j["status"] == "done", j.get("result", {}).get("label", j.get("error")))
    chk("audio spectrogram+waveform", "spectrogram" in j["result"] and len(j["result"]["waveform"]) > 10)
    chk("audio digital-silence flagged", any("silence" in i["name"].lower() for i in j["result"]["indicators"]))
    # video
    if HAS_CV2:
        vp = Path(tf.mkdtemp()) / "t.mp4"; vw = cv2.VideoWriter(str(vp), cv2.VideoWriter_fourcc(*"mp4v"), 10, (160, 120))
        for k in range(100): vw.write(np.full((120, 160, 3), 40 if k < 50 else 220, np.uint8) + rng.integers(0, 10, (120, 160, 3), dtype=np.uint8))
        vw.release(); r = up(vp.read_bytes(), "t.mp4", "video"); chk("video upload", r.status_code == 201)
        j = run("video", r.get_json()["file_id"]); chk("video analysis", j["status"] == "done", j.get("result", {}).get("label", j.get("error")))
        chk("video timeline+metadata", j["status"] == "done" and len(j["result"]["timeline"]) > 5 and j["result"]["metadata"]["frames"] == 100)
        chk("single cut does not label video as manipulated", j["result"]["label"] != LABELS[1], j["result"]["label"])
    # text
    r = up(b"Breaking news! Shocking leaked footage exposed in 2019. Reportedly 5 people were there, allegedly 12 people were there too, sources say it is a miracle.", "cap.txt", "text")
    chk("text upload", r.status_code == 201); j = run("text", r.get_json()["file_id"]); chk("text analysis", j["status"] == "done" and j["result"]["indicators"], j.get("result", {}).get("label", j.get("error")))
    chk("short text -> insufficient", run("text", up(b"too short", "s.txt", "text").get_json()["file_id"])["result"]["label"] == LABELS[3])
    # correlation, history, dashboard, reports
    cr = c.post("/api/correlate", json={"investigation_id": inv}); chk("correlation", cr.status_code == 200 and cr.get_json()["relations"], str(cr.get_json()["summary"]))
    chk("correlate unknown inv 404", c.post("/api/correlate", json={"investigation_id": "INV-NOPE00000"}).status_code == 404)
    chk("history", len(c.get("/api/investigations").get_json()) == 1 and c.get("/api/investigations/" + inv).status_code == 200)
    st = c.get("/api/dashboard/stats").get_json(); chk("dashboard from DB", st["investigations"] == 1 and st["files"] >= 4 and st["analyzed"]["image"] == 1)
    rp = c.get(f"/api/reports/{inv}/download?format=pdf"); chk("PDF report", rp.status_code == 200 and rp.data[:4] == b"%PDF", f"{len(rp.data)} bytes")
    rj = c.get(f"/api/reports/{inv}/download?format=json"); chk("JSON report", rj.status_code == 200 and "investigation" in rj.get_json())
    chk("path traversal blocked", c.get("/api/file/..%2f..%2fapp.py").status_code == 404 and c.get("/api/reports/../x/download").status_code in (400, 404))
    chk("frontend served", b"Veridex" in c.get("/").data)
    c.delete("/api/investigations/" + inv)
    print(f"\n{sum(res)}/{len(res)} checks passed"); return all(res)

if __name__ == "__main__":
    init_db()
    # clean stale temp working copies (>1 day) from processed/
    for p in PROCESSED.iterdir():
        try:
            if time.time() - p.stat().st_mtime > 86400: shutil.rmtree(p, ignore_errors=True) if p.is_dir() else p.unlink()
        except OSError: pass
    if "--selftest" in sys.argv: sys.exit(0 if selftest() else 1)
    port = int(os.environ.get("PORT", 5000))
    print(f"\n Veridex running at http://127.0.0.1:{port}   (Ctrl+C to stop)\n")
    if not os.environ.get("VERIDEX_NO_BROWSER"): threading.Timer(1.5, lambda: webbrowser.open(f"http://127.0.0.1:{port}")).start()
    app.run(host="127.0.0.1", port=port, threaded=True, debug=False)
