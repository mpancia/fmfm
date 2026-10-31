// Headless test of build/web/dinghy.wasm (run by `make test`). It boots the firmware and drives it like the panel:
// the lanes make sound alone, PLAY stops every note, the menu pages and the preset browser change what they
// should and nothing else, a saved patch loads back unchanged, every note algorithm, a chord progression and
// every Braids shape run without the firmware or the Lean runtime failing.
import fs from 'fs';
const mod = await WebAssembly.compile(fs.readFileSync('build/web/dinghy.wasm'));
const BTN = { PLAY: 12, EDIT: 6, SEQ: 11, GLO: 7, HOME: 8, SAVE: 9 };
const ENC = { SELECT: 0, ALGORITHM: 1, K1: 2, K2: 3, K3: 4, K4: 5, PRESETS: 6 };
let mem, inp, ms = 0, reports = [], frame = new Uint16Array(240 * 240);
const peaks = new Map();                               // half-second -> loudest sample in it
const events = [];                                     // [ms, fn(dataview)]
const shots = {};
const at = (t, fn) => events.push([t, fn]);
const press = (id) => (d) => d.setUint32(8, d.getUint32(8, true) | 1 << id, true);
const turn = (enc, n) => (d) => d.setInt32(16 + 4 * enc, n, true);
const shot = (name) => () => { shots[name] = frame; };
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
    const half = Math.floor(ms / 500); peaks.set(half, Math.max(peaks.get(half) ?? 0, p));
  },
  js_frame(ptr) { frame = new Uint16Array(mem.buffer.slice(ptr, ptr + 240 * 240 * 2)); },
  js_report(ptr, fatal) {
    const b = new Uint8Array(mem.buffer, ptr); let n = 0; while (b[n]) n++;
    reports.push((fatal ? 'FATAL ' : '') + Buffer.from(b.subarray(0, n)).toString());
  },
} };

// 0-0.8 s: the startup screen; a button press at 0.8 s skips it. Then it plays on its own until 4 s.
at(800, press(BTN.HOME));
at(400, shot('boot'));
// 0-4 s: it plays on its own. 4-6 s: stopped, so screens can be compared.
at(4000, press(BTN.PLAY));
at(4100, press(BTN.HOME)); at(4150, shot('home'));
at(4200, press(BTN.EDIT)); at(4250, shot('sound page'));
at(4300, turn(ENC.PRESETS, 1)); at(4400, shot('sound browser'));               // PRESETS in EDIT: sounds
at(4450, turn(ENC.SELECT, 2)); at(4550, shot('family'));                       // SELECT: another family
at(4600, press(BTN.HOME)); at(4650, shot('home 2'));                           // a button closes the browser
at(4700, press(BTN.EDIT)); at(4750, turn(ENC.K1, 1)); at(4800, press(BTN.HOME)); at(4850, shot('home shape'));
at(4900, turn(ENC.PRESETS, 1)); at(5000, shot('patch browser'));               // PRESETS in HOME: patches
at(5050, press(BTN.HOME)); at(5100, shot('patch'));
at(5150, press(BTN.SAVE));                                                      // keep it in user slot 1
at(5200, turn(ENC.PRESETS, 1)); at(5250, press(BTN.HOME)); at(5300, shot('other'));
at(5350, turn(ENC.PRESETS, -1)); at(5400, press(BTN.HOME)); at(5450, shot('loaded'));
at(6000, press(BTN.PLAY));
// every note algorithm on lane 1, one after another (SEQ, SEQ: the NOTES page; knob 1 is the algorithm)
at(6200, press(BTN.SEQ)); at(6250, press(BTN.SEQ)); at(6300, turn(ENC.K1, -6));
for (let i = 0; i < 6; i++) at(6500 + i * 1000, i === 0 ? () => {} : turn(ENC.K1, 1));
for (let i = 0; i < 6; i++) at(6600 + i * 1000, turn(ENC.K2, 3));                // a longer loop or bigger walk each time
// a chord progression and a key change (GLO: HARMONY; knob 1 key, 3 chords)
at(12500, press(BTN.GLO)); at(12600, turn(ENC.K3, 2)); at(12700, turn(ENC.K1, 3));
at(17000, turn(ENC.K3, 2));
// every Braids shape in turn (EDIT: SOUND; knob 1 is the shape)
at(20000, press(BTN.EDIT));
for (let i = 0; i < 47; i++) at(20100 + i * 200, turn(ENC.K1, 1));
const END = 30000;
events.sort((a, b) => a[0] - b[0]);
const inst = await WebAssembly.instantiate(mod, imports);
mem = inst.exports.memory; inp = inst.exports.web_in_ptr();
try { inst.exports.web_run(); } catch (e) { if (e.message !== 'done') throw e; }

const peak = (from, to) => Math.max(...[...peaks].filter(([h]) => h * 500 >= from && h * 500 < to).map(([, p]) => p), 0);
const changed = (a, b) => a.reduce((c, v, i) => c + (v !== b[i]), 0);
const ok = (name, cond) => { console.log((cond ? 'PASS ' : 'FAIL ') + name); if (!cond) process.exitCode = 1; };
const region = (f, y0, y1) => f.slice(y0 * 240, y1 * 240);
const row = (f, r) => region(f, 22 + r * 38, 22 + r * 38 + 36);
const sameRows = (a, b, rows) => rows.every((r) => changed(row(a, r), row(b, r)) === 0);
const audible = (from, to) => { let n = 0, all = 0; for (let t = from; t < to; t += 500) { all++; if (peak(t, t + 500) > 200) n++; } return [n, all]; };

ok('the startup screen draws Alfred and the title', changed(shots.boot, new Uint16Array(240 * 240)) > 3000);
ok('lanes make sound with no key pressed', peak(1000, 4000) > 1000);
ok('PLAY stops all sound (no stuck note)', peak(4500, 6000) === 0);
ok('the preset browser opens over the page', changed(shots['sound page'], shots['sound browser']) > 1500);
ok('SELECT in the browser chooses another family', changed(shots['sound browser'], shots.family) > 500);
ok('a button closes the browser', changed(shots['sound page'], shots['home 2']) > 0 && changed(shots.family, shots['home 2']) > 1500);
ok('the SOUND page shape knob changes the chosen lane only', changed(row(shots['home 2'], 0), row(shots['home shape'], 0)) > 0 &&
   sameRows(shots['home 2'], shots['home shape'], [1, 2, 3]));
ok('PRESETS on HOME opens the patch browser', changed(shots['home shape'], shots['patch browser']) > 1500);
ok('another patch changes every lane row', [0, 1, 2, 3].every((r) => changed(row(shots['home shape'], r), row(shots.patch, r)) > 0));
ok('a different slot looks different', changed(row(shots.patch, 1), row(shots.other, 1)) > 0);
ok('a saved patch loads back exactly', sameRows(shots.patch, shots.loaded, [0, 1, 2, 3]));
ok('PLAY starts it again', peak(6500, 7500) > 1000);
const algo = audible(6500, 12500);
ok(`every note algorithm keeps playing (${algo[0]} of ${algo[1]} half-seconds audible)`, algo[0] >= 0.75 * algo[1]);
const chords = audible(12500, 20000);
ok(`a chord progression keeps playing (${chords[0]} of ${chords[1]} half-seconds audible)`, chords[0] >= 0.75 * chords[1]);
const shapes = audible(20500, 29500);
ok(`every shape plays without crashing the firmware (${shapes[0]} of ${shapes[1]} half-seconds audible)`, shapes[0] >= 0.8 * shapes[1]);
ok('no Lean runtime reports', reports.length === 0);
console.log({ reports });
