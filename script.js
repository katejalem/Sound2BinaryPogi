"use strict";
/* Exact spec formulas:
   T_ms = 1000/freq | wave = 343/freq | levels = 2^bits
   time = i*T_ms/samples | height = amp*sin(2*PI*i/samples)
   level = round(((height+1)/2)*(levels-1)) | binary = padStart(bits) */
const $ = (id) => document.getElementById(id);
const els = {
  freq: $("freq"), amp: $("amp"), samples: $("samples"), bits: $("bits"),
  error: $("error"), mAmp: $("mAmp"), mFreq: $("mFreq"), mPeriod: $("mPeriod"),
  mWave: $("mWave"), placeholder: $("factsPlaceholder"),
  body: $("sampleBody"), binary: $("binaryOutput"), total: $("totalBits"),
  testBody: $("testBody"), canvas: $("waveCanvas"), pause: $("pauseBtn"),
  dot: $("liveDot"), audio: $("audioStatus"),
  modeSynthetic: $("modeSynthetic"), modeUpload: $("modeUpload"),
  modeNote: $("modeNote"), inputsSub: $("inputsSub"),
  uploadBlock: $("uploadBlock"), mp3File: $("mp3File"), dropzone: $("dropzone"),
  dzFile: $("dzFile"), fileMeta: $("fileMeta"), uploadAudio: $("uploadAudio"),
  synthWrap: $("synthWaveWrap"), uploadWrap: $("uploadWaveWrap"),
  uploadCanvas: $("uploadCanvas"), uploadWindowLabel: $("uploadWindowLabel"),
  uploadDesc: $("uploadDesc"), fieldFreq: $("fieldFreq"),
  lblAmp: $("lblAmp"), lblFreq: $("lblFreq"), lblPeriod: $("lblPeriod"), lblWave: $("lblWave"),
  factsSub: $("factsSub"), sampleSub: $("sampleSub"), binarySub: $("binarySub"),
  playLabel: $("playLabel"), convertLabel: $("convertLabel")
};
const MAX_MP3_BYTES = 12 * 1024 * 1024;
const UPLOAD_WINDOW_SEC = 1.0;
const UPLOAD_PLAY_SEC = 10.0;
let currentExcerpt = null;
let mode = "synthetic";
let uploadBuffer = null, uploadFileName = "", uploadURL = null, decoding = false;
const PRESETS = {
  check: { f: 1000, a: 1, n: 4, b: 2 },
  a: { f: 440, a: 0.8, n: 8, b: 3 },
  b: { f: 200, a: 0.5, n: 6, b: 4 },
  c: { f: 500, a: 0.9, n: 5, b: 3 }
};
const TESTS = [
  { name: "A", ...PRESETS.a }, { name: "B", ...PRESETS.b }, { name: "C", ...PRESETS.c }
];
let lastResult = null, lastBinary = "", phase = 0;
let playing = true;
try {
  if (window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches) playing = false;
} catch (e) { /* keep animation on */ }

function fmtPeriod(f) { return (1000 / f).toFixed(2) + " ms"; }
function fmtWave(f) {
  const m = 343 / f;
  return m >= 1 ? m.toFixed(2) + " m" : (m * 100).toFixed(1) + " cm";
}
function quantize(height, bits) {
  const levels = Math.pow(2, bits);
  const level = Math.round(((height + 1) / 2) * (levels - 1));
  return { level, bin: level.toString(2).padStart(bits, "0") };
}
function computeSamples(freq, amp, n, bits) {
  const T = 1000 / freq, rows = [];
  for (let i = 0; i < n; i++) {
    const time = (i * T) / n;
    const height = amp * Math.sin((2 * Math.PI * i) / n);
    const q = quantize(height, bits);
    rows.push({ n: i + 1, time, height, level: q.level, bin: q.bin });
  }
  return { T, wave: 343 / freq, total: n * bits, rows, seq: rows.map((r) => r.bin).join(" ") };
}
/* Upload path: first UPLOAD_WINDOW_SEC seconds, box-averaged to N samples */
function computeUploadSamples(buffer, n, bits, gain) {
  const sr = buffer.sampleRate;
  const windowSamples = Math.min(buffer.length, Math.max(1, Math.floor(sr * UPLOAD_WINDOW_SEC)));
  const windowMs = (windowSamples / sr) * 1000;
  const chans = [];
  for (let c = 0; c < buffer.numberOfChannels; c++) chans.push(buffer.getChannelData(c));
  let peak = 0;
  for (let i = 0; i < windowSamples; i++) {
    let s = 0;
    for (let c = 0; c < chans.length; c++) s += chans[c][i];
    s /= chans.length;
    const a = Math.abs(s);
    if (a > peak) peak = a;
  }
  if (!(peak > 1e-4)) peak = 1e-4;
  const step = Math.max(1, Math.floor(windowSamples / n));
  const rows = [];
  for (let i = 0; i < n; i++) {
    const center = Math.min(windowSamples - 1, Math.floor(((i + 0.5) * windowSamples) / n));
    const start = Math.max(0, center - Math.floor(step / 2));
    const end = Math.min(windowSamples, start + step);
    let sum = 0;
    for (let k = start; k < end; k++) {
      let s = 0;
      for (let c = 0; c < chans.length; c++) s += chans[c][k];
      sum += s / chans.length;
    }
    const avg = sum / Math.max(1, end - start);
    const height = Math.max(-1, Math.min(1, (avg / peak) * gain));
    const time = (i * windowMs) / n;
    const q = quantize(height, bits);
    rows.push({ n: i + 1, time, height, level: q.level, bin: q.bin });
  }
  return { windowMs, sampleRate: sr, channels: buffer.numberOfChannels, total: n * bits, rows, seq: rows.map((r) => r.bin).join(" ") };
}
function readInputs() {
  const f = parseFloat(els.freq.value), a = parseFloat(els.amp.value);
  const n = Number(els.samples.value), b = Number(els.bits.value);
  if (!isFinite(f) || !isFinite(a) || els.freq.value === "" || els.amp.value === "")
    return { err: "Please fill in all fields with valid numbers." };
  if (!(f > 0)) return { err: "Frequency must be greater than 0." };
  if (!(a >= 0 && a <= 1)) return { err: "Amplitude must be between 0 and 1." };
  if (!Number.isInteger(n) || n < 2 || n > 64) return { err: "Samples must be a whole number from 2 to 64." };
  if (!Number.isInteger(b) || b < 1 || b > 8) return { err: "Bits must be a whole number from 1 to 8." };
  return { f, a, n, b };
}
function showError(msg) {
  if (!msg) { els.error.hidden = true; els.error.textContent = ""; return; }
  els.error.hidden = false; els.error.textContent = msg;
}
function render(result, f, a) {
  lastResult = result; lastBinary = result.seq;
  setFactLabels("Amplitude", "Frequency", "Period", "Wavelength");
  els.mAmp.textContent = String(a);
  els.mFreq.textContent = String(f) + " Hz";
  els.mPeriod.textContent = fmtPeriod(f);
  els.mWave.textContent = fmtWave(f);
  els.factsSub.textContent = "Measured from your inputs";
  els.sampleSub.textContent = "One row per sample, snapshot at phase zero";
  els.binarySub.textContent = "Single-line output, one space between values";
  els.placeholder.style.display = "none";
  els.body.innerHTML = result.rows.map((r) =>
    `<tr><td>${r.n}</td><td>${r.time.toFixed(2)}</td><td>${r.height.toFixed(2)}</td><td>${r.level}</td><td class="mono">${r.bin}</td></tr>`
  ).join("");
  els.binary.textContent = result.seq;
  els.total.textContent = String(result.total);
}
function setFactLabels(a, f, p, w) {
  if (els.lblAmp) els.lblAmp.textContent = a;
  if (els.lblFreq) els.lblFreq.textContent = f;
  if (els.lblPeriod) els.lblPeriod.textContent = p;
  if (els.lblWave) els.lblWave.textContent = w;
}
function renderUpload(result, gain) {
  lastResult = result; lastBinary = result.seq;
  setFactLabels("Gain", "Source", "Window", "Sample rate");
  els.mAmp.textContent = String(gain);
  els.mFreq.textContent = "MP3";
  els.mPeriod.textContent = result.windowMs.toFixed(2) + " ms";
  els.mWave.textContent = (result.sampleRate / 1000).toFixed(1) + " kHz";
  els.factsSub.textContent = "First " + (result.windowMs / 1000).toFixed(2) + "s of " + (uploadFileName || "your MP3");
  els.sampleSub.textContent = "One row per sample, averaged over first " + result.windowMs.toFixed(0) + " ms";
  els.binarySub.textContent = "Single-line output from your MP3, one space between values";
  els.placeholder.style.display = "none";
  els.body.innerHTML = result.rows.map((r) =>
    `<tr><td>${r.n}</td><td>${r.time.toFixed(2)}</td><td>${r.height.toFixed(2)}</td><td>${r.level}</td><td class="mono">${r.bin}</td></tr>`
  ).join("");
  els.binary.textContent = result.seq;
  els.total.textContent = String(result.total);
  if (els.uploadWindowLabel) els.uploadWindowLabel.textContent = result.windowMs.toFixed(0) + " ms window · " + result.channels + "ch · " + (result.sampleRate / 1000).toFixed(1) + " kHz";
}
function readUploadInputs() {
  const a = parseFloat(els.amp.value);
  const n = Number(els.samples.value), b = Number(els.bits.value);
  if (!isFinite(a) || els.amp.value === "") return { err: "Please fill in amplitude with a valid number." };
  if (!(a >= 0 && a <= 1)) return { err: "Amplitude must be between 0 and 1." };
  if (!Number.isInteger(n) || n < 2 || n > 64) return { err: "Samples must be a whole number from 2 to 64." };
  if (!Number.isInteger(b) || b < 1 || b > 8) return { err: "Bits must be a whole number from 1 to 8." };
  return { a, n, b };
}
function doConvert() {
  if (mode === "upload") return doConvertUpload();
  const v = readInputs();
  if (v.err) { showError(v.err); return false; }
  showError(null);
  render(computeSamples(v.f, v.a, v.n, v.b), v.f, v.a);
  return true;
}
function doConvertUpload() {
  if (!uploadBuffer) { showError("Choose an MP3 file first, then press Convert."); return false; }
  const v = readUploadInputs();
  if (v.err) { showError(v.err); return false; }
  showError(null);
  renderUpload(computeUploadSamples(uploadBuffer, v.n, v.b, v.a), v.a);
  drawUploadWave();
  return true;
}
function setMode(m) {
  mode = m;
  const isUpload = m === "upload";
  els.modeSynthetic.setAttribute("aria-pressed", String(!isUpload));
  els.modeUpload.setAttribute("aria-pressed", String(isUpload));
  els.uploadBlock.hidden = !isUpload;
  els.synthWrap.hidden = isUpload;
  if (!isUpload) els.uploadWrap.hidden = true;
  else if (uploadBuffer) els.uploadWrap.hidden = false;
  els.freq.disabled = isUpload;
  els.fieldFreq.classList.toggle("disabled", isUpload);
  els.inputsSub.textContent = isUpload ? "Upload settings — first 1 second of your MP3" : "Wave settings — synthetic sine tone";
  els.modeNote.textContent = isUpload
    ? "MP3 mode: first 1s is box-averaged to N samples, then quantized with the same levels + binary code. Frequency is ignored. Play gives the first 10s."
    : "Synthetic mode: one full sine wave sampled evenly over its period.";
  if (els.playLabel) els.playLabel.textContent = isUpload ? "Play Excerpt (10s)" : "Play Tone (1s)";
  showError(null);
}
function renderTests() {
  els.testBody.innerHTML = TESTS.map((t) => {
    const r = computeSamples(t.f, t.a, t.n, t.b);
    return `<tr><td><strong>${t.name}</strong></td><td>${t.f} Hz</td><td>${t.a}</td><td>${t.n}</td><td>${t.b}</td><td>${fmtPeriod(t.f)}</td><td>${fmtWave(t.f)}</td><td>${r.total}</td><td>${r.seq}</td></tr>`;
  }).join("");
}
function sizeCanvas() {
  const dpr = Math.min(window.devicePixelRatio || 1, 2);
  const w = els.canvas.clientWidth || els.canvas.parentElement.clientWidth - 24;
  els.canvas.width = Math.max(280, w) * dpr;
  els.canvas.height = 240 * dpr;
  sizeUploadCanvas(dpr);
}
function sizeUploadCanvas(dpr) {
  if (!els.uploadCanvas) return;
  const ratio = dpr || Math.min(window.devicePixelRatio || 1, 2);
  const w = els.uploadCanvas.clientWidth || (els.uploadCanvas.parentElement ? els.uploadCanvas.parentElement.clientWidth - 28 : 300);
  els.uploadCanvas.width = Math.max(280, w) * ratio;
  els.uploadCanvas.height = 160 * ratio;
}
function drawWave() {
  const ctx = els.canvas.getContext("2d");
  const W = els.canvas.width, H = els.canvas.height, mid = H / 2;
  const v = readInputs();
  const amp = v.err ? parseFloat(els.amp.value) || 0 : v.a;
  const n = v.err ? parseInt(els.samples.value, 10) || 4 : v.n;
  const count = Number.isInteger(n) && n >= 2 && n <= 64 ? n : 4;
  ctx.clearRect(0, 0, W, H);
  ctx.strokeStyle = "rgba(15,23,42,.12)"; ctx.lineWidth = 1;
  ctx.beginPath(); ctx.moveTo(0, mid); ctx.lineTo(W, mid); ctx.stroke();
  ctx.strokeStyle = "#2563eb"; ctx.lineWidth = Math.max(2, W / 300);
  ctx.shadowColor = "rgba(37,99,235,.4)"; ctx.shadowBlur = 10;
  ctx.beginPath();
  for (let x = 0; x <= W; x += 3) {
    const t = (x / W) * Math.PI * 2 + phase;
    const y = mid - Math.max(-1, Math.min(1, amp)) * Math.sin(t) * (H * 0.38);
    x === 0 ? ctx.moveTo(x, y) : ctx.lineTo(x, y);
  }
  ctx.stroke(); ctx.shadowBlur = 0;
  ctx.fillStyle = "#f59e0b";
  for (let i = 0; i < count; i++) {
    const frac = i / count, x = frac * W;
    const t = frac * Math.PI * 2 + phase;
    const y = mid - Math.max(-1, Math.min(1, amp)) * Math.sin(t) * (H * 0.38);
    ctx.beginPath(); ctx.arc(x, y, Math.max(4, W / 160), 0, Math.PI * 2); ctx.fill();
    ctx.strokeStyle = "#1e293b"; ctx.lineWidth = 2; ctx.stroke();
  }
}
function loop() { if (playing && mode === "synthetic") { phase += 0.03; drawWave(); } requestAnimationFrame(loop); }
let audioCtx = null;
function ensureAudio() {
  audioCtx = audioCtx || new (window.AudioContext || window.webkitAudioContext)();
  if (audioCtx.state === "suspended") audioCtx.resume();
  return audioCtx;
}
function currentUploadSampleDots() {
  if (!uploadBuffer) return [];
  const v = readUploadInputs();
  const n = v.err ? parseInt(els.samples.value, 10) || 4 : v.n;
  const gain = v.err ? parseFloat(els.amp.value) || 1 : v.a;
  const count = Number.isInteger(n) && n >= 2 && n <= 64 ? n : 4;
  const r = computeUploadSamples(uploadBuffer, count, 8, Math.max(0, Math.min(1, gain)));
  return r.rows.map((row, i) => ({ frac: (i + 0.5) / count, height: row.height }));
}
function drawUploadWave() {
  if (!els.uploadCanvas || !uploadBuffer) return;
  const ctx = els.uploadCanvas.getContext("2d");
  const W = els.uploadCanvas.width, H = els.uploadCanvas.height, mid = H / 2;
  const sr = uploadBuffer.sampleRate;
  const windowSamples = Math.min(uploadBuffer.length, Math.floor(sr * UPLOAD_WINDOW_SEC));
  const ch0 = uploadBuffer.getChannelData(0);
  const buckets = Math.max(60, Math.min(240, Math.floor(W / 4)));
  ctx.clearRect(0, 0, W, H);
  ctx.strokeStyle = "rgba(15,23,42,.12)"; ctx.lineWidth = 1;
  ctx.beginPath(); ctx.moveTo(0, mid); ctx.lineTo(W, mid); ctx.stroke();
  ctx.strokeStyle = "#059669"; ctx.lineWidth = Math.max(2, W / 400);
  ctx.shadowColor = "rgba(5,150,105,.35)"; ctx.shadowBlur = 8;
  ctx.beginPath();
  for (let b = 0; b < buckets; b++) {
    const start = Math.floor((b * windowSamples) / buckets);
    const end = Math.min(windowSamples, Math.floor(((b + 1) * windowSamples) / buckets));
    let mn = 1, mx = -1;
    for (let k = start; k < end; k += Math.max(1, Math.floor((end - start) / 8))) {
      const v = ch0[k] || 0;
      if (v < mn) mn = v;
      if (v > mx) mx = v;
    }
    const x = (b / (buckets - 1)) * W;
    const y1 = mid - mx * (H * 0.38), y2 = mid - mn * (H * 0.38);
    if (b === 0) ctx.moveTo(x, (y1 + y2) / 2);
    else ctx.lineTo(x, (y1 + y2) / 2);
  }
  ctx.stroke(); ctx.shadowBlur = 0;
  const dots = currentUploadSampleDots();
  ctx.fillStyle = "#f59e0b";
  dots.forEach((d) => {
    const x = d.frac * W, y = mid - Math.max(-1, Math.min(1, d.height)) * (H * 0.38);
    ctx.beginPath(); ctx.arc(x, y, Math.max(4, W / 160), 0, Math.PI * 2); ctx.fill();
    ctx.strokeStyle = "#1e293b"; ctx.lineWidth = 2; ctx.stroke();
  });
}
function fmtBytes(b) {
  if (b < 1024) return b + " B";
  if (b < 1024 * 1024) return (b / 1024).toFixed(1) + " KB";
  return (b / (1024 * 1024)).toFixed(2) + " MB";
}
function isMp3File(file) {
  const t = (file.type || "").toLowerCase();
  const n = (file.name || "").toLowerCase();
  return t === "audio/mpeg" || t === "audio/mp3" || t === "audio/x-mp3" || n.endsWith(".mp3") || t.startsWith("audio/");
}
async function handleFile(file) {
  if (decoding) return;
  if (!file) { showError("Choose an MP3 file first."); return; }
  if (!isMp3File(file)) { showError("That file is not an MP3. Please choose a .mp3 file."); return; }
  if (file.size === 0) { showError("That file is empty."); return; }
  if (file.size > MAX_MP3_BYTES) { showError("File is " + fmtBytes(file.size) + " — please choose an MP3 up to 12MB."); return; }
  decoding = true;
  els.fileMeta.textContent = "Decoding " + file.name + "…";
  try {
    const ctx = ensureAudio();
    const ab = await file.arrayBuffer();
    const decoded = await ctx.decodeAudioData(ab.slice(0));
    uploadBuffer = decoded;
    uploadFileName = file.name;
    if (uploadURL) URL.revokeObjectURL(uploadURL);
    uploadURL = URL.createObjectURL(file);
    els.uploadAudio.src = uploadURL;
    els.uploadAudio.hidden = false;
    els.dzFile.textContent = file.name + " · " + fmtBytes(file.size);
    const dur = decoded.duration.toFixed(2);
    const truncated = decoded.duration > UPLOAD_WINDOW_SEC ? " (first 1.00s used)" : "";
    els.fileMeta.textContent = file.name + " · " + dur + "s · " + (decoded.sampleRate / 1000).toFixed(1) + " kHz · " + decoded.numberOfChannels + "ch" + truncated;
    els.uploadWrap.hidden = false;
    sizeUploadCanvas();
    drawUploadWave();
    showError(null);
    doConvertUpload();
  } catch (e) {
    uploadBuffer = null;
    els.uploadWrap.hidden = true;
    els.uploadAudio.hidden = true;
    showError("Could not decode that MP3. It may be corrupt or protected. Try another file.");
  } finally {
    decoding = false;
    if (els.mp3File) els.mp3File.value = "";
  }
}
function playTone(dur) {
  const f = parseFloat(els.freq.value);
  if (!isFinite(f) || !(f > 0)) { showError("Frequency must be greater than 0 before playing."); return; }
  try {
    const ctx = ensureAudio();
    const osc = ctx.createOscillator(), gain = ctx.createGain();
    osc.type = "sine"; osc.frequency.value = f;
    gain.gain.setValueAtTime(0.0001, ctx.currentTime);
    gain.gain.exponentialRampToValueAtTime(0.4, ctx.currentTime + 0.02);
    gain.gain.exponentialRampToValueAtTime(0.0001, ctx.currentTime + (dur || 1));
    osc.connect(gain); gain.connect(ctx.destination);
    osc.start(); osc.stop(ctx.currentTime + (dur || 1));
    els.audio.textContent = "Playing " + f + " Hz for 1s.";
    setTimeout(() => { els.audio.textContent = ""; }, 1500);
  } catch (e) { els.audio.textContent = "Audio is unavailable in this browser."; }
}
function playExcerpt() {
  if (!uploadBuffer) { showError("Choose an MP3 file first, then play."); return; }
  try {
    const ctx = ensureAudio();
    if (currentExcerpt) { try { currentExcerpt.stop(); } catch (e) { /* already stopped */ } }
    const src = ctx.createBufferSource();
    src.buffer = uploadBuffer;
    const gain = ctx.createGain();
    const t0 = ctx.currentTime;
    const dur = Math.min(UPLOAD_PLAY_SEC, uploadBuffer.duration);
    gain.gain.setValueAtTime(0.0001, t0);
    gain.gain.exponentialRampToValueAtTime(0.5, t0 + 0.03);
    if (dur > 0.6) gain.gain.setValueAtTime(0.5, t0 + dur - 0.3);
    gain.gain.exponentialRampToValueAtTime(0.0001, t0 + dur);
    src.connect(gain); gain.connect(ctx.destination);
    src.start(0, 0, dur);
    src.stop(t0 + dur + 0.05);
    currentExcerpt = src;
    src.onended = () => { if (currentExcerpt === src) currentExcerpt = null; };
    els.audio.textContent = "Playing first " + dur.toFixed(dur < 10 ? 2 : 0) + "s of " + (uploadFileName || "MP3") + ".";
    setTimeout(() => { els.audio.textContent = ""; }, 3000);
  } catch (e) { els.audio.textContent = "Audio is unavailable in this browser."; }
}
function playCurrent() {
  if (mode === "upload") playExcerpt();
  else playTone(1);
}
async function copyBinary(btn) {
  if (!lastBinary) { showError("Press Convert first, then copy the binary result."); return; }
  const done = () => { const o = btn.textContent; btn.textContent = "Copied!"; setTimeout(() => { btn.textContent = o; }, 1200); };
  try { await navigator.clipboard.writeText(lastBinary); done(); }
  catch (e) {
    const ta = document.createElement("textarea");
    ta.value = lastBinary; document.body.appendChild(ta); ta.select();
    try { document.execCommand("copy"); done(); } catch (x) { showError("Copy is unavailable in this browser."); }
    ta.remove();
  }
}
$("convertBtn").addEventListener("click", doConvert);
$("footConvert").addEventListener("click", () => { doConvert(); document.getElementById("inputs").scrollIntoView({ behavior: "smooth" }); });
$("playBtn").addEventListener("click", playCurrent);
$("playBtnFoot").addEventListener("click", playCurrent);
$("copyBtn").addEventListener("click", (e) => copyBinary(e.target));
$("copyBtnTop").addEventListener("click", (e) => copyBinary(e.target));
els.modeSynthetic.addEventListener("click", () => setMode("synthetic"));
els.modeUpload.addEventListener("click", () => setMode("upload"));
els.mp3File.addEventListener("change", (e) => { const f = e.target.files && e.target.files[0]; if (f) handleFile(f); });
els.dropzone.addEventListener("click", () => els.mp3File.click());
els.dropzone.addEventListener("keydown", (e) => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); els.mp3File.click(); } });
["dragenter", "dragover"].forEach((ev) => els.dropzone.addEventListener(ev, (e) => { e.preventDefault(); els.dropzone.classList.add("dragover"); }));
["dragleave", "drop"].forEach((ev) => els.dropzone.addEventListener(ev, (e) => { e.preventDefault(); els.dropzone.classList.remove("dragover"); }));
els.dropzone.addEventListener("drop", (e) => { const f = e.dataTransfer && e.dataTransfer.files && e.dataTransfer.files[0]; if (f) handleFile(f); });
document.querySelectorAll("[data-preset]").forEach((ch) => ch.addEventListener("click", () => {
  document.querySelectorAll("[data-preset]").forEach((c) => c.setAttribute("aria-pressed", "false"));
  ch.setAttribute("aria-pressed", "true");
  setMode("synthetic");
  const p = PRESETS[ch.dataset.preset];
  els.freq.value = p.f; els.amp.value = p.a; els.samples.value = p.n; els.bits.value = p.b;
  drawWave();
  doConvert();
}));
function syncPauseUI() {
  els.pause.textContent = playing ? "Pause animation" : "Resume animation";
  els.pause.setAttribute("aria-pressed", String(playing));
  els.dot.classList.toggle("paused", !playing);
}
els.pause.addEventListener("click", () => {
  playing = !playing;
  syncPauseUI();
  if (playing) drawWave();
});
window.addEventListener("resize", () => { sizeCanvas(); drawWave(); if (uploadBuffer && mode === "upload") drawUploadWave(); });
["freq", "amp", "samples", "bits"].forEach((id) => $(id).addEventListener("input", () => {
  if (mode === "upload" && uploadBuffer && (id === "samples" || id === "amp")) drawUploadWave();
  else if (mode === "synthetic") drawWave();
}));
sizeCanvas(); drawWave(); renderTests(); syncPauseUI(); setMode("synthetic"); loop(); doConvert();
