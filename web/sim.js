'use strict';
/* Page side of the FM-1 simulator. The firmware runs in worker.js, audio plays in worklet.js; all three share
 * these buffers.
 *   ctl (Int32Array):  0 notes held   1 buttons held   2 button press edges   3 button release edges
 *                      4..10 encoder detents   11 MIDI write index   12 MIDI read index   13 audio frames written
 *                      14 audio frames read   15,16 LEDs (lo, hi)   17 screen frame counter   18 audio underruns
 *                      19 simulated ms   20 a patch to load (index + 1)   21 the patch playing
 *                      22 the Demo button (1 start, 2 stop)   23 AUTO is on
 *                      32..95 MIDI queue (status | d1 << 8 | d2 << 16 | source << 24)
 *   ring: 16-bit stereo audio.   frame: 240x240 RGB565. */
const RING = 16384;
const BUTTONS = ['OCT-', 'OCT+', 'FX', 'SEL', 'ENV', 'LFO', 'EDIT', 'GLO', 'HOME', 'SAVE', 'ARP', 'SEQ', 'PLAY', 'REC'];
const BUTTON_HELP = {
  'OCT-': 'keys an octave down', 'OCT+': 'keys an octave up',
  FX: 'REVERB page, again for DELAY', SEL: 'mute the chosen lane', ENV: 'ENVELOPE page', LFO: 'LFO page for the chosen lane',
  EDIT: 'SOUND page, again for FILTER, ENVELOPE, MIX, PAN', GLO: 'HARMONY page, again for SYSTEM, MIDI, BANKS',
  HOME: 'the four lanes', SAVE: 'save the patch to the chosen slot', ARP: 'the arpeggiator, again to latch or for QUANT',
  SEQ: 'RHYTHM page, again for FEEL, NOTES, RANGE', PLAY: 'start or stop', REC: 'PUNCH: the keys as momentary effects',
};
const ENCODERS = ['Select', 'Algorithm', 'Knob 1', 'Knob 2', 'Knob 3', 'Knob 4', 'Presets'];
const ENCODER_HELP = ['the lane (in a browser: the group)', 'tempo (in the sound browser: the grouping)',
  'the first value on screen', 'the second value', 'the third value', 'the fourth value', 'open the browser and scroll'];
const PLAY = 12, HOME = 8, SELECT = 0;
const NKEYS = 27, FIRST_MIDI = 53;                       // key 0 = F3
const NOTE = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];
const isBlack = (k) => [1, 3, 6, 8, 10].includes((FIRST_MIDI + k) % 12);
const keyName = (k) => NOTE[(FIRST_MIDI + k) % 12] + (Math.floor((FIRST_MIDI + k) / 12) - 1);

// computer keyboard -> key index (C4 = 7)
const PC_KEYS = {};
'zsxdcvgbhnjm,l.;/'.split('').forEach((c, i) => { PC_KEYS[c] = 7 + i; });
'q2w3er5t'.split('').forEach((c, i) => { PC_KEYS[c] = 19 + i; });

const $ = (id) => document.getElementById(id);
let noteUntil = 0;                                           // a message that should outlast the running ticker
const status = (t) => { if (performance.now() >= noteUntil) $('status').textContent = t; };
const note = (t, ms = 4000) => { $('status').textContent = t; noteUntil = performance.now() + ms; };

let ctl, ring, frame, worker, audio, gain, analyser, running = false, lastFrame = 0, lastLeds = [0, 0];
const mouseKeys = new Set(), pcKeys = new Set();
const keyEls = [], ledKey = [], ledBtn = [], btnEls = [], encStep = [];

// ---- input -> shared state ----
function pushNotes() {
  let m = 0;
  for (const k of mouseKeys) m |= 1 << k;
  for (const k of pcKeys) m |= 1 << k;
  Atomics.store(ctl, 0, m);
  keyEls.forEach((el, k) => el.classList.toggle('down', (m >> k & 1) === 1));
}
function buttonDown(id) {
  tourInput(); tourPage(id);
  Atomics.or(ctl, 1, 1 << id); Atomics.or(ctl, 2, 1 << id); btnEls[id].classList.add('down');
}
function buttonUp(id) {
  Atomics.and(ctl, 1, ~(1 << id)); Atomics.or(ctl, 3, 1 << id); btnEls[id].classList.remove('down');
}
function turn(enc, d) { tourInput(); Atomics.add(ctl, 4 + enc, d); }
function midiPush(st, d1, d2, src) {
  const w = Atomics.load(ctl, 11), r = Atomics.load(ctl, 12);
  if (((w - r) | 0) >= 64) return;                       // queue full: drop
  Atomics.store(ctl, 32 + (w & 63), st | d1 << 8 | d2 << 16 | src << 24);
  Atomics.store(ctl, 11, (w + 1) | 0);
}

// ---- build the panel ----
function build() {
  const keys = $('keys');
  let whites = 0;
  for (let k = 0; k < NKEYS; k++) {
    const el = document.createElement('div');
    el.className = 'key ' + (isBlack(k) ? 'black' : 'white');
    el.setAttribute('role', 'button'); el.setAttribute('aria-label', keyName(k));
    const led = document.createElement('span'); led.className = 'led'; el.append(led);
    if (isBlack(k)) el.style.left = `calc(${whites} * 100% / 16 - 100% / 16 * .3 + 1px)`; else whites++;
    el.addEventListener('pointerdown', (e) => {
      el.setPointerCapture(e.pointerId); tourInput(); mouseKeys.add(k); pushNotes();
    });
    const up = () => { mouseKeys.delete(k); pushNotes(); };
    el.addEventListener('pointerup', up); el.addEventListener('pointercancel', up);
    keys.append(el); keyEls.push(el); ledKey.push(led);
  }
  BUTTONS.forEach((name, id) => {
    const wrap = document.createElement('div'); wrap.className = 'btn';
    const led = document.createElement('span'); led.className = 'led';
    const b = document.createElement('button'); b.type = 'button'; b.textContent = name; b.title = BUTTON_HELP[name];
    b.addEventListener('pointerdown', (e) => { b.setPointerCapture(e.pointerId); buttonDown(id); });
    b.addEventListener('pointerup', () => buttonUp(id)); b.addEventListener('pointercancel', () => buttonUp(id));
    b.addEventListener('keydown', (e) => { if ((e.key === ' ' || e.key === 'Enter') && !e.repeat) { e.preventDefault(); buttonDown(id); } });
    b.addEventListener('keyup', (e) => { if (e.key === ' ' || e.key === 'Enter') buttonUp(id); });
    wrap.append(led, b); $('buttons').append(wrap); ledBtn.push(led); btnEls.push(b);
  });
  ENCODERS.forEach((name, id) => {
    const wrap = document.createElement('div'); wrap.className = 'enc';
    const knob = document.createElement('div'); knob.className = 'knob'; knob.tabIndex = 0;
    knob.setAttribute('role', 'spinbutton'); knob.setAttribute('aria-label', name); knob.title = ENCODER_HELP[id];
    let pos = 0, y0 = null, moved = false;
    const step = (d) => { pos += d; knob.style.setProperty('--rot', pos * 14 + 'deg'); turn(id, d); };
    knob.addEventListener('wheel', (e) => { e.preventDefault(); step(e.deltaY < 0 ? 1 : -1); }, { passive: false });
    knob.addEventListener('pointerdown', (e) => { knob.setPointerCapture(e.pointerId); y0 = e.clientY; moved = false; });
    knob.addEventListener('pointermove', (e) => {
      if (y0 === null) return;
      const d = Math.trunc((y0 - e.clientY) / 8);
      if (d) { step(d); y0 = e.clientY; moved = true; }
    });
    knob.addEventListener('pointerup', (e) => {
      if (!moved) { const r = knob.getBoundingClientRect(); step(e.clientX >= r.left + r.width / 2 ? 1 : -1); }
      y0 = null;
    });
    knob.addEventListener('keydown', (e) => {
      if (e.key === 'ArrowRight' || e.key === 'ArrowUp') { e.preventDefault(); step(1); }
      if (e.key === 'ArrowLeft' || e.key === 'ArrowDown') { e.preventDefault(); step(-1); }
    });
    const label = document.createElement('span'); label.textContent = name;
    wrap.append(knob, label); $('encoders').append(wrap); encStep.push(step);
  });
}

const KEY_BUTTON = { '-': 0, '=': 1, ' ': PLAY, Escape: HOME };          // held like the panel button
const inField = (e) => ['INPUT', 'SELECT', 'TEXTAREA'].includes(e.target.tagName);
function loadPatch(i) {
  const n = $('patch').options.length;
  if (!running || !n) return;
  tourInput();
  i = ((i % n) + n) % n;
  $('patch').value = String(i); Atomics.store(ctl, 20, i + 1);
}
document.addEventListener('keydown', (e) => {
  if (!running || e.repeat || e.ctrlKey || e.metaKey || e.altKey || inField(e)) return;
  if (e.key in KEY_BUTTON) { e.preventDefault(); buttonDown(KEY_BUTTON[e.key]); return; }
  if (e.key === '[' || e.key === ']') { turn(SELECT, e.key === ']' ? 1 : -1); return; }
  if (e.key === 'PageUp' || e.key === 'PageDown') { e.preventDefault(); loadPatch(Number($('patch').value) + (e.key === 'PageDown' ? 1 : -1)); return; }
  const c = e.key.toLowerCase();
  if (c in PC_KEYS) { tourInput(); pcKeys.add(PC_KEYS[c]); pushNotes(); }
});
document.addEventListener('keyup', (e) => {
  if (!running) return;
  if (e.key in KEY_BUTTON) { buttonUp(KEY_BUTTON[e.key]); return; }
  const c = e.key.toLowerCase();
  if (c in PC_KEYS) { pcKeys.delete(PC_KEYS[c]); pushNotes(); }
});
window.addEventListener('blur', () => { pcKeys.clear(); mouseKeys.clear(); if (running) pushNotes(); });

// ---- screen ----
const ctx = $('screen').getContext('2d');
const img = ctx.createImageData(240, 240);
function draw(now) {
  requestAnimationFrame(draw);
  if (!running) return;
  drawScope(now);
  const n = Atomics.load(ctl, 17);
  if (n !== lastFrame) {
    lastFrame = n;
    const px = img.data;
    for (let i = 0; i < 240 * 240; i++) {
      const c = frame[i];
      px[i * 4] = (c >> 11) * 255 / 31; px[i * 4 + 1] = ((c >> 5) & 63) * 255 / 63; px[i * 4 + 2] = (c & 31) * 255 / 31; px[i * 4 + 3] = 255;
    }
    ctx.putImageData(img, 0, 0);
    const lo = Atomics.load(ctl, 15), hi = Atomics.load(ctl, 16);
    if (lo !== lastLeds[0] || hi !== lastLeds[1]) {
      lastLeds = [lo, hi];
      for (let id = 0; id < 14; id++) ledBtn[id].classList.toggle('lit', (lo >>> id & 1) === 1);
      for (let k = 0; k < NKEYS; k++) { const b = 14 + k; ledKey[k].classList.toggle('lit', ((b < 32 ? lo >>> b : hi >>> (b - 32)) & 1) === 1); }
    }
    const under = Atomics.load(ctl, 18);
    status(`Running: ${(Atomics.load(ctl, 19) / 1000).toFixed(1)} s of firmware time` + (under ? `, ${under} audio dropouts (browser too busy)` : ''));
    const playing = Atomics.load(ctl, 21);                     // the device's own browser may have changed the patch
    if (document.activeElement !== $('patch') && String(playing) !== $('patch').value) $('patch').value = String(playing);
    if (demoWanted && Atomics.load(ctl, 19) > 1000) { demoWanted = false; Atomics.store(ctl, 22, 1); }
    if (patchWanted !== null && Atomics.load(ctl, 19) > 1000) { loadPatch(patchWanted); patchWanted = null; }
    $('demo').textContent = Atomics.load(ctl, 23) ? 'Stop demo' : 'Demo';
    $('demo').classList.toggle('on', !!Atomics.load(ctl, 23));
  }
}

// ---- scope ----
// One ink line of what leaves the gain node: ~30 fps, one read into a buffer allocated once, drawn from the first
// rising zero crossing so a steady tone stands still.
const scope = $('scope'), sctx = scope.getContext('2d'), scopeBuf = new Float32Array(2048);
let lastScope = 0;
function sizeScope() {
  const dpr = window.devicePixelRatio || 1;
  const w = Math.round(scope.clientWidth * dpr), h = Math.round(scope.clientHeight * dpr);
  if (scope.width !== w || scope.height !== h) { scope.width = w; scope.height = h; }
  sctx.lineWidth = Math.max(1, Math.round(dpr)); sctx.strokeStyle = '#000'; sctx.lineJoin = 'round';
}
let scopePeak = 0;                                            // the trace fills the strip at any level: it ranges
function drawScope(now) {                                    // on the last frame's peak, let down slowly
  if (now - lastScope < 33) return;
  lastScope = now;
  sizeScope();
  const W = scope.width, H = scope.height, mid = H / 2, span = scopeBuf.length / 2;
  analyser.getFloatTimeDomainData(scopeBuf);
  let t = 0;
  for (let i = 1; i < span; i++) if (scopeBuf[i - 1] < 0 && scopeBuf[i] >= 0) { t = i; break; }
  const scale = (mid - 2) / Math.max(scopePeak, .02);
  let peak = scopePeak * .96;
  sctx.clearRect(0, 0, W, H);
  sctx.beginPath();
  for (let x = 0; x < W; x++) {
    const v = scopeBuf[t + ((x * span / W) | 0)], a = v < 0 ? -v : v;
    if (a > peak) peak = a;
    const y = Math.min(H - 1, Math.max(1, mid - v * scale));
    if (x) sctx.lineTo(x, y); else sctx.moveTo(x, y);
  }
  sctx.stroke();
  scopePeak = peak;
}
function flatScope() {                                       // powered off: a resting trace
  sizeScope();
  const mid = Math.round(scope.height / 2) + .5;
  sctx.clearRect(0, 0, scope.width, scope.height);
  sctx.beginPath(); sctx.moveTo(0, mid); sctx.lineTo(scope.width, mid); sctx.stroke();
}
window.addEventListener('resize', () => { if (!running) flatScope(); });

// ---- power ----
async function powerOn() {
  if (!crossOriginIsolated) { status('This page must be served by tools/serve_web.py (needs SharedArrayBuffer). Run make run.'); return; }
  $('power').disabled = true;
  ctl = new Int32Array(new SharedArrayBuffer(4 * 128));
  ring = new Int16Array(new SharedArrayBuffer(2 * 2 * RING));
  frame = new Uint16Array(new SharedArrayBuffer(2 * 240 * 240));
  lastFrame = 0; lastLeds = [0, 0];
  audio = new AudioContext({ sampleRate: 44100, latencyHint: 'interactive' });
  await audio.audioWorklet.addModule('worklet.js');
  const node = new AudioWorkletNode(audio, 'fm1-out', { outputChannelCount: [2], processorOptions: { ctl: ctl.buffer, ring: ring.buffer, ringFrames: RING } });
  gain = audio.createGain(); gain.gain.value = $('vol').value / 100;
  analyser = audio.createAnalyser(); analyser.fftSize = scopeBuf.length; analyser.smoothingTimeConstant = 0;
  node.connect(gain).connect(audio.destination);
  gain.connect(analyser);
  await audio.resume();
  worker = new Worker('worker.js');
  worker.onmessage = (e) => {
    if (e.data.error) powerOff('Firmware stopped: ' + e.data.error);
    else if (e.data.report !== undefined) { if (e.data.fatal) powerOff('Lean runtime stopped the firmware: ' + e.data.report); else status('Lean: ' + e.data.report); }
    else if (e.data.watch) {
      $('watch').tBodies[0].replaceChildren(...e.data.watch.map(([name, checks, fails]) => {
        const tr = document.createElement('tr'), link = document.createElement('a');
        link.href = `https://github.com/mpancia/fmfm/blob/main/docs/PROOFS.md`; link.title = 'in docs/PROOFS.md'; link.textContent = name;
        tr.insertCell().append(link);
        tr.insertCell().textContent = checks.toLocaleString() + ' checks';
        const f = tr.insertCell();
        f.textContent = fails ? fails.toLocaleString() + ' failed' : checks ? 'held' : 'not yet';
        f.className = fails ? 'fail' : checks ? 'held' : 'wait';
        return tr;
      }));
    }
    else if (e.data.ready) {
      running = true; $('off').hidden = true; $('power').textContent = 'Power off'; $('power').disabled = false; status('Booting...');
      $('scope-wrap').classList.add('live');
      const sel = $('patch');
      sel.replaceChildren(...e.data.patches.map((name, i) => new Option(`${i + 1}  ${name}`, i)));
      sel.disabled = false;
      for (const id of ['record', 'shot', 'share', 'tour']) $(id).disabled = false;
      tourReset();
    }
  };
  worker.postMessage({ ctl: ctl.buffer, ring: ring.buffer, frame: frame.buffer, base: location.href });
}
function powerOff(why) {
  running = false;
  if (worker) worker.terminate();
  if (audio) audio.close();
  worker = audio = gain = analyser = tap = null;
  $('scope-wrap').classList.remove('live'); flatScope();
  mouseKeys.clear(); pcKeys.clear();
  keyEls.forEach((el) => el.classList.remove('down'));
  [...ledBtn, ...ledKey].forEach((l) => l.classList.remove('lit'));
  $('off').hidden = false; $('power').textContent = 'Power on'; $('power').disabled = false;
  $('patch').disabled = true;
  if (recorder) stopRecording();
  for (const id of ['record', 'shot', 'share', 'tour']) $(id).disabled = true;
  tourStop();
  $('demo').textContent = 'Demo'; $('demo').classList.remove('on');
  status(why || 'Off. Power on to boot the firmware (the firmware\'s saved settings are lost when it powers off).');
}
$('power').addEventListener('click', () => (running ? powerOff() : powerOn()));
$('vol').addEventListener('input', () => { if (gain) gain.gain.value = $('vol').value / 100; });
$('patch').addEventListener('change', () => {
  if (running) { tourInput(); Atomics.store(ctl, 20, Number($('patch').value) + 1); }
  $('patch').blur();
});
let demoWanted = false;                                      // Demo pressed while off: start AUTO once the firmware is up
const linkPatch = new URLSearchParams(location.search).get('patch');   // ?patch=N (1-based, as the list shows)
let patchWanted = linkPatch && Number(linkPatch) >= 1 ? Number(linkPatch) - 1 : null;
if (patchWanted !== null) status(`Off. Power on to boot the firmware and load patch ${linkPatch}.`);
$('demo').addEventListener('click', async () => {
  if (!running) { demoWanted = true; await powerOn(); return; }
  tourInput(); Atomics.store(ctl, 22, Atomics.load(ctl, 23) ? 2 : 1);
});

$('midi').addEventListener('click', async () => {
  if (!navigator.requestMIDIAccess) { note('This browser has no Web MIDI. Use Chrome or Edge.'); return; }
  try {
    const access = await navigator.requestMIDIAccess();
    const hook = () => {
      let n = 0;
      access.inputs.forEach((inp) => {
        n++;
        inp.onmidimessage = (m) => { if (running && m.data.length) midiPush(m.data[0], m.data[1] || 0, m.data[2] || 0, 1); };
      });
      $('midi').textContent = n ? `MIDI in: ${n} device${n > 1 ? 's' : ''}` : 'No MIDI devices';
    };
    access.onstatechange = hook; hook();
  } catch (err) { note('MIDI access refused: ' + err.message); }
});

// ---- record, screenshot, link ----
let recorder = null, tap = null;
const download = (blob, name) => {
  const a = document.createElement('a'); a.href = URL.createObjectURL(blob); a.download = name; a.click();
  setTimeout(() => URL.revokeObjectURL(a.href), 10000);
};
const patchName = () => ($('patch').selectedOptions[0]?.textContent || 'fm1').replace(/^\d+\s+/, '').toLowerCase().replace(/\W+/g, '-');
function stopRecording() {
  recorder.stop(); recorder = null;
  $('record').textContent = 'Record'; $('record').classList.remove('on');
}
$('record').addEventListener('click', () => {
  if (recorder) { stopRecording(); return; }
  if (!window.MediaRecorder) { note('This browser cannot record audio.'); return; }
  if (!tap) { tap = audio.createMediaStreamDestination(); gain.connect(tap); }
  const chunks = [];
  recorder = new MediaRecorder(tap.stream, { mimeType: MediaRecorder.isTypeSupported('audio/webm;codecs=opus') ? 'audio/webm;codecs=opus' : '' });
  recorder.ondataavailable = (e) => chunks.push(e.data);
  recorder.onstop = () => download(new Blob(chunks, { type: 'audio/webm' }), `formalfred-${patchName()}.webm`);
  recorder.start();
  $('record').textContent = 'Stop recording'; $('record').classList.add('on');
  note('Recording what you hear; Stop recording saves a .webm.');
});
$('shot').addEventListener('click', () => $('screen').toBlob((b) => download(b, `formalfred-${patchName()}.png`)));
$('share').addEventListener('click', async () => {
  const url = new URL(location.href); url.searchParams.set('patch', String(Number($('patch').value) + 1));
  try { await navigator.clipboard.writeText(url.toString()); note(`Copied ${url}`); }
  catch { history.replaceState(null, '', url); note(`Link: ${url}`); }
});

// ---- the tour ----
// A guided walk for someone who has never seen the panel: the page presses the buttons and turns the knobs, and a
// caption under the device says what the screen shows. The firmware remembers each group's last page (goto_group in
// dinghy.c), so the tour keeps the same model, fed by every press, to reach a page with the right number of taps.
// Its own input is marked (`tour.own`); anyone else's stops it.
const SEQ = 11, EDIT = 6, GLO = 7, FX = 2, ENV = 4, REC = 13, KNOB1 = 2, KNOB3 = 4;
const PAGES = { [HOME]: ['HOME'], [SEQ]: ['RHYTHM', 'FEEL', 'NOTES', 'RANGE'], [FX]: ['REVERB', 'DELAY'],
  [EDIT]: ['SOUND', 'FILTER', 'ENVELOPE', 'MIX', 'PAN'], [GLO]: ['HARMONY', 'SYSTEM', 'MIDI', 'BANKS'], 5: ['LFO'],
  10: ['ARP', 'QUANT'], [REC]: ['PUNCH'] };
const tour = { run: 0, own: false, group: HOME, index: 0, memo: {}, keys: new Set(), btn: -1 };
const STOPPED = Symbol('tour stopped');
let tourSeq = 0;
function tourReset() { tour.group = HOME; tour.index = 0; tour.memo = {}; }
function tourPage(id) {                                      // what a press does to the page, as dinghy.c does it
  if (id === ENV) { tour.group = EDIT; tour.index = 2; tour.memo[EDIT] = 2; }
  else if (id === REC) { tour.group = tour.group === REC ? HOME : REC; tour.index = 0; }
  else if (id in PAGES) {
    tour.index = tour.group === id ? (tour.index + 1) % PAGES[id].length : tour.memo[id] || 0;
    tour.group = id; tour.memo[id] = tour.index;
  }
}
function tourInput() { if (tour.run && !tour.own) tourStop(); }
function tourStop() {
  if (!tour.run) return;
  tour.run = 0;
  if (tour.btn >= 0) { buttonUp(tour.btn); tour.btn = -1; }
  if (tour.keys.size) { for (const k of tour.keys) mouseKeys.delete(k); tour.keys.clear(); if (running) pushNotes(); }
  $('tour').classList.remove('on'); $('tour-strip').hidden = true;
}
function tourApi(me) {                                       // the script's verbs; each stops dead once `me` is over
  const live = () => { if (tour.run !== me) throw STOPPED; };
  const own = (f) => { tour.own = true; try { f(); } finally { tour.own = false; } };
  const sleep = (ms) => new Promise((res) => setTimeout(res, ms)).then(live);
  const press = async (id) => {
    live(); own(() => buttonDown(id)); tour.btn = id;
    await sleep(80);
    tour.btn = -1; buttonUp(id);
    await sleep(160);
  };
  const goto = async (g, i) => {                             // tap the group button until its page `i` is up
    const n = PAGES[g].length;
    let k = tour.group === g ? (i - tour.index + n) % n : 1 + (i - (tour.memo[g] || 0) + n) % n;
    while (k--) await press(g);
  };
  const knob = async (enc, d) => {                           // a few detents at a time, so the screen is seen to follow
    for (let left = d; left; ) {
      const c = Math.max(-4, Math.min(4, left));
      left -= c; own(() => encStep[enc](c));
      await sleep(60);
    }
  };
  const hold = async (keys, ms) => {
    for (const k of keys) { tour.keys.add(k); mouseKeys.add(k); }
    pushNotes(); await sleep(ms);
    for (const k of keys) { tour.keys.delete(k); mouseKeys.delete(k); }
    pushNotes();
  };
  const patch = (i) => own(() => loadPatch(i));
  const playing = () => (lastLeds[0] >>> PLAY & 1) === 1;
  const say = async (i, html) => {
    const strip = $('tour-strip'), text = strip.querySelector('.say');
    if (!strip.hidden) { text.classList.add('out'); await sleep(220); }
    strip.querySelector('.n').textContent = `${i + 1} / ${TOUR.length}`; text.innerHTML = html;
    strip.hidden = false; text.classList.remove('out');
  };
  return { sleep, press, goto, knob, hold, patch, playing, say };
}
// The script. Captions describe the boot patch, CLOCKWORK, which step 1 loads; knob moves are relative, so they
// hold for whichever lane is chosen. The last step loads it again, so the tour leaves the patch as it found it.
const TOUR = [
  { do: async (t) => {
      if (Atomics.load(ctl, 23)) Atomics.store(ctl, 22, 2);  // the demo would change the patch under the captions
      await t.press(HOME); t.patch(0); await t.sleep(300);
      if (!t.playing()) await t.press(PLAY);
    },
    say: '<b>HOME</b>: the boot patch, CLOCKWORK. Four lanes; each row is a lane\'s bar, its hits in colour and the ' +
      'step playing in white. Below, the key, the chord of the moment, and PLAYING.', wait: 7000 },
  { do: async (t) => { await t.goto(SEQ, 0); await t.knob(KNOB1, 2); },
    say: '<b>SEQ</b>, RHYTHM: the chosen lane\'s bar as a circle. HITS up two: the rhythm is Euclidean, so the hits ' +
      'spread as evenly over the steps as whole steps allow.', wait: 7000 },
  { do: async (t) => { await t.goto(SEQ, 1); },
    say: '<b>SEQ</b> again, FEEL: where the rhythm comes from. EUCLID; ROTATE, the bar turned, with accents; ' +
      'AUTOMAT, a cellular automaton that steps a generation a bar; or RATCHET, each hit split.', wait: 7000 },
  { do: async (t) => { await t.goto(SEQ, 2); },
    say: '<b>SEQ</b> again, NOTES: ALGO is one of eleven note sources. Random, walks, loops, a TURING shift ' +
      'register, a MARKOV chain that learns from the keys, a GRAMMAR rewriting a phrase, chord tones.', wait: 7000 },
  { do: async (t) => { await t.goto(GLO, 0); await t.knob(KNOB3, 1); },
    say: '<b>GLO</b>, HARMONY: CHORDS is a progression written as degrees, now 6-4-1-5. The lanes that follow it ' +
      'take chords stacked from the key\'s scale, so they stay in key: a theorem.', wait: 8000 },
  { do: async (t) => { await t.goto(EDIT, 0); await t.knob(KNOB1, -70); await t.knob(KNOB1, 50); },
    say: '<b>EDIT</b>, SOUND: SHAPE runs down through the 48 Braids shapes and back up past them into the 8 FM ' +
      'voices, to FM BASS. After those come 10 808 drums.', wait: 8000 },
  { do: async (t) => { await t.goto(EDIT, 1); await t.knob(KNOB1, -25); },
    say: '<b>EDIT</b> again, FILTER: CUTOFF down, and the lane darkens. Every voice runs through this state-variable ' +
      'filter; fully open with no resonance it is an exact bypass, which is a theorem.', wait: 7000 },
  { do: async (t) => { await t.goto(FX, 0); await t.knob(KNOB1, 6); },
    say: '<b>FX</b>, REVERB: SEND up, more of this lane into the reverb, Clouds\' network in fixed point with its ' +
      'arithmetic in Lean. An undriven tail shrinks every trip round the loops: a theorem.', wait: 7000 },
  { do: async (t) => { await t.goto(REC, 0); await t.sleep(600); await t.hold([2, 9], 2600); },
    say: '<b>REC</b>, PUNCH: while this page is up the keys are momentary effects. STUTTER and WASH, held for a bar; ' +
      'let go and it is gone. With nothing held every effect is the identity, which is a theorem.', wait: 5000 },
  { do: async (t) => {
      await t.goto(HOME, 0); t.patch(0);
      $('watch').scrollIntoView({ behavior: 'smooth', block: 'nearest' });
    },
    say: '<b>HOME</b> again, and the patch as it booted. Below, the proofs, watched: twelve of the theorems\' ' +
      'statements, checked on the running machine as it plays and counted.', wait: 9000 },
];
async function tourStart() {
  const me = tour.run = ++tourSeq, t = tourApi(me);
  $('tour').classList.add('on');
  try {
    for (let i = 0; i < TOUR.length; i++) {
      await t.say(i, TOUR[i].say);
      if (i === 0) $('tour-strip').scrollIntoView({ behavior: 'smooth', block: 'nearest' });
      await TOUR[i].do(t);
      await t.sleep(TOUR[i].wait);
    }
  } catch (e) { if (e !== STOPPED) throw e; }
  if (tour.run === me) tourStop();
}
$('tour').addEventListener('click', () => { if (tour.run) tourStop(); else tourStart(); $('tour').blur(); });

build();
flatScope();
requestAnimationFrame(draw);
