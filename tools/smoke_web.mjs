// Headless test of build/web/dinghy.wasm (run by `make test`): boots the firmware and checks that the lanes
// make sound by themselves, that PLAY stops every note, that the screen moves, that the sound, shape and patch
// controls change what they should and nothing else, that a saved patch loads back unchanged, and that the Lean
// runtime never reports a problem.
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
const ENC = { SELECT: 0, ALGORITHM: 1, PRESETS: 6 };
const BTN = { EDIT: 6, HOME: 8, SAVE: 9 };
const turn = (enc, n) => (d) => d.setInt32(16 + 4 * enc, n, true);
const hold = (id, on) => (d) => d.setUint32(4, on ? 1 << id : 0, true);
const shot = (name) => () => { shots[name] = frame; };
// while stopped (4000..6000 ms) nothing moves, so screens can be compared
at(4100, shot('start'));
at(4200, turn(ENC.PRESETS, 1));                       // next sound for lane 1
at(4300, shot('sound'));
at(4400, press(BTN.EDIT));
at(4500, turn(ENC.ALGORITHM, 1));                     // SOUND page: next shape for lane 1
at(4600, shot('shape'));
at(4700, hold(BTN.HOME, true)); at(4720, turn(ENC.PRESETS, 1)); at(4740, hold(BTN.HOME, false));   // next patch
at(4800, shot('patch'));
at(4850, press(BTN.SAVE));                            // keep it in a user slot
at(4900, hold(BTN.HOME, true)); at(4920, turn(ENC.PRESETS, 1)); at(4940, hold(BTN.HOME, false));   // another slot
at(5000, shot('other'));
at(5050, hold(BTN.HOME, true)); at(5070, turn(ENC.PRESETS, -1)); at(5090, hold(BTN.HOME, false));  // back to ours
at(5200, shot('loaded'));
for (let i = 0; i < 47; i++) at(9000 + i * 200, turn(ENC.ALGORITHM, 1));   // every Braids shape in turn, SOUND page
const END = 18500;
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
const region = (f, y0, y1) => f.slice(y0 * 240, y1 * 240);
const row = (f, r) => region(f, 22 + r * 40, 22 + r * 40 + 38);
const panel = (f) => region(f, 184, 240);
const sameRows = (a, b, rows) => rows.every((r) => changed(row(a, r), row(b, r)) === 0);
ok('PRESETS changes the panel, not the lane rows', changed(panel(shots.start), panel(shots.sound)) > 0 &&
   sameRows(shots.start, shots.sound, [0, 1, 2, 3]));
ok('ALGORITHM on the SOUND page changes the shape of the chosen lane only', changed(row(shots.sound, 0), row(shots.shape, 0)) > 0 &&
   sameRows(shots.sound, shots.shape, [1, 2, 3]));
ok('another patch changes every lane row', [0, 1, 2, 3].every((r) => changed(row(shots.shape, r), row(shots.patch, r)) > 0));
ok('a different slot looks different', changed(row(shots.patch, 1), row(shots.other, 1)) > 0);
ok('a saved patch loads back exactly', sameRows(shots.patch, shots.loaded, [0, 1, 2, 3]));
const windows = []; for (let t = 9500; t < 18000; t += 500) windows.push(peak(t, t + 500));
ok('every shape plays without crashing the firmware (' + windows.filter((p) => p > 200).length + ' of ' + windows.length + ' half-seconds audible)',
   windows.filter((p) => p > 200).length >= 0.8 * windows.length);
ok('no Lean runtime reports', reports.length === 0);
console.log({ peakBefore: peak(500, 4000), peakStopped: peak(4500, 6000), peakAfter: peak(6500, 9000), reports });
