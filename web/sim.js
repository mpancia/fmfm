'use strict';
/* Page side of the FM-1 simulator. The firmware runs in worker.js, audio plays in worklet.js; all three share
 * these buffers.
 *   ctl (Int32Array):  0 notes held   1 buttons held   2 button press edges   3 button release edges
 *                      4..10 encoder detents   11 MIDI write index   12 MIDI read index   13 audio frames written
 *                      14 audio frames read   15,16 LEDs (lo, hi)   17 screen frame counter   18 audio underruns
 *                      19 simulated ms   32..95 MIDI queue (status | d1 << 8 | d2 << 16 | source << 24)
 *   ring: 16-bit stereo audio.   frame: 240x240 RGB565. */
const RING = 16384;
const BUTTONS = ['OCT-', 'OCT+', 'FX', 'SEL', 'ENV', 'LFO', 'EDIT', 'GLO', 'HOME', 'SAVE', 'ARP', 'SEQ', 'PLAY', 'REC'];
const ENCODERS = ['Select', 'Algorithm', 'Knob 1', 'Knob 2', 'Knob 3', 'Knob 4', 'Presets'];
const NKEYS = 27, FIRST_MIDI = 53;                       // key 0 = F3
const NOTE = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];
const isBlack = (k) => [1, 3, 6, 8, 10].includes((FIRST_MIDI + k) % 12);
const keyName = (k) => NOTE[(FIRST_MIDI + k) % 12] + (Math.floor((FIRST_MIDI + k) / 12) - 1);

// computer keyboard -> key index (C4 = 7)
const PC_KEYS = {};
'zsxdcvgbhnjm,l.;/'.split('').forEach((c, i) => { PC_KEYS[c] = 7 + i; });
'q2w3er5t'.split('').forEach((c, i) => { PC_KEYS[c] = 19 + i; });

const $ = (id) => document.getElementById(id);
const status = (t) => { $('status').textContent = t; };

let ctl, ring, frame, worker, audio, gain, running = false, lastFrame = 0, lastLeds = [0, 0];
const mouseKeys = new Set(), pcKeys = new Set();
const keyEls = [], ledKey = [], ledBtn = [], btnEls = [];

// ---- input -> shared state ----
function pushNotes() {
  let m = 0;
  for (const k of mouseKeys) m |= 1 << k;
  for (const k of pcKeys) m |= 1 << k;
  Atomics.store(ctl, 0, m);
  keyEls.forEach((el, k) => el.classList.toggle('down', (m >> k & 1) === 1));
}
function buttonDown(id) {
  Atomics.or(ctl, 1, 1 << id); Atomics.or(ctl, 2, 1 << id); btnEls[id].classList.add('down');
}
function buttonUp(id) {
  Atomics.and(ctl, 1, ~(1 << id)); Atomics.or(ctl, 3, 1 << id); btnEls[id].classList.remove('down');
}
function turn(enc, d) { Atomics.add(ctl, 4 + enc, d); }
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
    el.addEventListener('pointerdown', (e) => { el.setPointerCapture(e.pointerId); mouseKeys.add(k); pushNotes(); });
    const up = () => { mouseKeys.delete(k); pushNotes(); };
    el.addEventListener('pointerup', up); el.addEventListener('pointercancel', up);
    keys.append(el); keyEls.push(el); ledKey.push(led);
  }
  BUTTONS.forEach((name, id) => {
    const wrap = document.createElement('div'); wrap.className = 'btn';
    const led = document.createElement('span'); led.className = 'led';
    const b = document.createElement('button'); b.type = 'button'; b.textContent = name;
    b.addEventListener('pointerdown', (e) => { b.setPointerCapture(e.pointerId); buttonDown(id); });
    b.addEventListener('pointerup', () => buttonUp(id)); b.addEventListener('pointercancel', () => buttonUp(id));
    b.addEventListener('keydown', (e) => { if ((e.key === ' ' || e.key === 'Enter') && !e.repeat) { e.preventDefault(); buttonDown(id); } });
    b.addEventListener('keyup', (e) => { if (e.key === ' ' || e.key === 'Enter') buttonUp(id); });
    wrap.append(led, b); $('buttons').append(wrap); ledBtn.push(led); btnEls.push(b);
  });
  ENCODERS.forEach((name, id) => {
    const wrap = document.createElement('div'); wrap.className = 'enc';
    const knob = document.createElement('div'); knob.className = 'knob'; knob.tabIndex = 0;
    knob.setAttribute('role', 'spinbutton'); knob.setAttribute('aria-label', name);
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
    wrap.append(knob, label); $('encoders').append(wrap);
  });
}

document.addEventListener('keydown', (e) => {
  if (!running || e.repeat || e.ctrlKey || e.metaKey || e.altKey) return;
  const c = e.key.toLowerCase();
  if (c === '-') { buttonDown(0); return; }
  if (c === '=') { buttonDown(1); return; }
  if (c in PC_KEYS) { pcKeys.add(PC_KEYS[c]); pushNotes(); }
});
document.addEventListener('keyup', (e) => {
  const c = e.key.toLowerCase();
  if (!running) return;
  if (c === '-') buttonUp(0); else if (c === '=') buttonUp(1);
  else if (c in PC_KEYS) { pcKeys.delete(PC_KEYS[c]); pushNotes(); }
});
window.addEventListener('blur', () => { pcKeys.clear(); mouseKeys.clear(); if (running) pushNotes(); });

// ---- screen ----
const ctx = $('screen').getContext('2d');
const img = ctx.createImageData(240, 240);
function draw() {
  requestAnimationFrame(draw);
  if (!running) return;
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
  }
}

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
  node.connect(gain).connect(audio.destination);
  await audio.resume();
  worker = new Worker('worker.js');
  worker.onmessage = (e) => {
    if (e.data.error) powerOff('Firmware failed to start: ' + e.data.error);
    else if (e.data.ready) { running = true; $('off').hidden = true; $('power').textContent = 'Power off'; $('power').disabled = false; status('Booting...'); }
  };
  worker.postMessage({ ctl: ctl.buffer, ring: ring.buffer, frame: frame.buffer, base: location.href });
}
function powerOff(why) {
  running = false;
  if (worker) worker.terminate();
  if (audio) audio.close();
  worker = audio = null;
  mouseKeys.clear(); pcKeys.clear();
  keyEls.forEach((el) => el.classList.remove('down'));
  [...ledBtn, ...ledKey].forEach((l) => l.classList.remove('lit'));
  $('off').hidden = false; $('power').textContent = 'Power on'; $('power').disabled = false;
  status(why || 'Off. Power on to boot the firmware (the firmware\'s saved settings are lost when it powers off).');
}
$('power').addEventListener('click', () => (running ? powerOff() : powerOn()));
$('vol').addEventListener('input', () => { if (gain) gain.gain.value = $('vol').value / 100; });

$('midi').addEventListener('click', async () => {
  if (!navigator.requestMIDIAccess) { status('This browser has no Web MIDI. Use Chrome or Edge.'); return; }
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
  } catch (err) { status('MIDI access refused: ' + err.message); }
});

build();
requestAnimationFrame(draw);
