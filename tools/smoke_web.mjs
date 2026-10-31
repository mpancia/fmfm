// Headless test of build/web/dinghy.wasm: boots the firmware, plays notes, checks sound, screen, LEDs and
// that the Lean note tracker drives the "last note" display. Run: node tools/smoke_web.mjs  (make test)
import fs from 'fs';
const mod = await WebAssembly.compile(fs.readFileSync('build/web/dinghy.wasm'));
let mem, inp, ms = 0, peak = 0, leds = 0, lastFrame = new Uint16Array(240 * 240), reports = [];
const script = [];                                    // [ms, fn(dv)]
const dv = () => new DataView(mem.buffer, inp);
const at = (t, fn) => script.push([t, fn]);
at(100, (d) => d.setUint32(0, 1 << 7, true));        // C4 down
at(900, (d) => d.setUint32(0, 0, true));             // up
at(1000, (d) => d.setUint32(0, 1 << 11, true));      // E4 down
at(1400, (d) => d.setUint32(0, 0, true));
const END = 1800;
const shots = {}, ledsAt = {};
at(800, () => { shots[800] = lastFrame; ledsAt[800] = leds; });     // C4 held
at(1300, () => { shots[1300] = lastFrame; ledsAt[1300] = leds; });   // E4 held
const imports = { env: {
  js_sync(t) { ms = t; while (script.length && script[0][0] <= t) script.shift()[1](dv()); if (t >= END) throw new Error('done'); },
  js_audio(ptr, n) { const a = new Int16Array(mem.buffer, ptr, n * 2); let p = 0; for (const v of a) p = Math.max(p, Math.abs(v)); peak = Math.max(peak, p); },
  js_frame(ptr, lo) { lastFrame = new Uint16Array(mem.buffer.slice(ptr, ptr + 240 * 240 * 2)); leds = lo; },
  js_report(ptr, fatal) { const b = new Uint8Array(mem.buffer, ptr); let n = 0; while (b[n]) n++; reports.push((fatal ? 'FATAL ' : '') + Buffer.from(b.subarray(0, n)).toString()); },
} };
script.sort((a, b) => a[0] - b[0]);
const inst = await WebAssembly.instantiate(mod, imports);
mem = inst.exports.memory; inp = inst.exports.web_in_ptr();
try { inst.exports.web_run(); } catch (e) { if (e.message !== 'done') throw e; }
const lit = (f) => f.reduce((c, v) => c + (v !== 0), 0);
const diff = (a, b) => a.reduce((c, v, i) => c + (v !== b[i]), 0);
const ok = (name, cond) => { console.log((cond ? 'PASS ' : 'FAIL ') + name); if (!cond) process.exitCode = 1; };
ok('boots and draws', lit(lastFrame) > 1000);
ok('plays sound', peak > 1000);
ok('key LEDs follow the keys (C4 = LED 21, E4 = LED 25)', (ledsAt[800] >>> 21 & 1) === 1 && (ledsAt[1300] >>> 25 & 1) === 1 && (ledsAt[1300] >>> 21 & 1) === 0);
ok('last-note display changes from C4 to E4 (tracker in Lean)', shots[800] && shots[1300] && diff(shots[800], shots[1300]) > 100);
ok('no Lean runtime reports', reports.length === 0);
console.log({ peak, reports });
