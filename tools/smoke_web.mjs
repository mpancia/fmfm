// Headless test of build/web/dinghy.wasm (run by `make test`): boots the firmware and checks that the lanes
// make sound by themselves, that PLAY stops every note, that the screen moves, and that the Lean runtime
// never reports a problem.
import fs from 'fs';
const mod = await WebAssembly.compile(fs.readFileSync('build/web/dinghy.wasm'));
const BTN_PLAY = 12, BTN_OCT_UP = 1;
let mem, inp, ms = 0, reports = [], frame = new Uint16Array(240 * 240);
const peaks = new Map();                               // second -> loudest sample in it
const frames = [];
const shots = {};
const events = [];                                     // [ms, fn(dataview)]
const at = (t, fn) => events.push([t, fn]);
const press = (id) => (d) => d.setUint32(8, d.getUint32(8, true) | 1 << id, true);
at(4000, press(BTN_PLAY));                             // stop
at(6000, press(BTN_PLAY));                             // start again
const PRESETS = 6;
at(4500, (d) => d.setInt32(16 + 4 * PRESETS, 1, true));   // while stopped: next voice for lane 1
at(4400, () => { shots.before = frame; });
at(4700, () => { shots.after = frame; });
const END = 9000;
const imports = { env: {
  js_sync(t) {
    ms = t;
    const d = new DataView(mem.buffer, inp);
    while (events.length && events[0][0] <= t) events.shift()[1](d);
    if (t >= END) throw new Error('done');
  },
  js_audio(ptr, n) {
    const a = new Int16Array(mem.buffer, ptr, n * 2);
    let p = 0; for (const v of a) p = Math.max(p, Math.abs(v));
    const sec = Math.floor(ms / 500); peaks.set(sec, Math.max(peaks.get(sec) ?? 0, p));
  },
  js_frame(ptr) { frame = new Uint16Array(mem.buffer.slice(ptr, ptr + 240 * 240 * 2)); if (ms % 500 < 20) frames.push(frame); },
  js_report(ptr, fatal) {
    const b = new Uint8Array(mem.buffer, ptr); let n = 0; while (b[n]) n++;
    reports.push((fatal ? 'FATAL ' : '') + Buffer.from(b.subarray(0, n)).toString());
  },
} };
events.sort((a, b) => a[0] - b[0]);
const inst = await WebAssembly.instantiate(mod, imports);
mem = inst.exports.memory; inp = inst.exports.web_in_ptr();
try { inst.exports.web_run(); } catch (e) { if (e.message !== 'done') throw e; }

const peak = (from, to) => Math.max(...[...peaks].filter(([s]) => s * 500 >= from && s * 500 < to).map(([, p]) => p), 0);
const changed = (a, b) => a.reduce((c, v, i) => c + (v !== b[i]), 0);
const ok = (name, cond) => { console.log((cond ? 'PASS ' : 'FAIL ') + name); if (!cond) process.exitCode = 1; };
ok('lanes make sound with no key pressed', peak(500, 4000) > 1000);
ok('PLAY stops all sound (no stuck note)', peak(4500, 6000) === 0);
ok('PLAY starts it again', peak(6500, 9000) > 1000);
ok('the screen changes as steps advance', frames.length > 4 && changed(frames[2], frames[3]) > 50);
const rowPixels = (f, row) => f.slice((22 + row * 42) * 240, (22 + row * 42 + 40) * 240);
const voiceChangedOnlyLane1 = shots.before && shots.after &&
  changed(rowPixels(shots.before, 0), rowPixels(shots.after, 0)) > 0 &&
  [1, 2, 3].every((r) => changed(rowPixels(shots.before, r), rowPixels(shots.after, r)) === 0);
ok('PRESETS changes the voice shown on the chosen lane only', voiceChangedOnlyLane1);
ok('no Lean runtime reports', reports.length === 0);
console.log({ peakBefore: peak(500, 4000), peakStopped: peak(4500, 6000), peakAfter: peak(6500, 9000), reports });
