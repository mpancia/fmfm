// Headless test of build/web/dinghy.wasm (run by `make test`). It boots the firmware and drives it like the panel:
// the lanes make sound alone, PLAY stops every note, the menu pages and the preset browser change what they
// should and nothing else, a saved patch loads back unchanged, every note algorithm, a chord progression and
// every Braids shape run without the firmware or the Lean runtime failing.
import fs from 'fs';
const mod = await WebAssembly.compile(fs.readFileSync(process.env.WASM || 'build/web/dinghy.wasm'));
const BTN = { PLAY: 12, EDIT: 6, SEQ: 11, GLO: 7, HOME: 8, SAVE: 9, FX: 2, LFO: 5, ENV: 4, REC: 13, ARP: 10 };
const ENC = { SELECT: 0, ALGORITHM: 1, K1: 2, K2: 3, K3: 4, K4: 5, PRESETS: 6 };
let mem, inp, ms = 0, reports = [], frame = new Uint16Array(240 * 240);
const peaks = new Map();                               // half-second -> loudest sample in it
const crossings = new Map();                           // half-second -> zero crossings (a brightness proxy)
const events = [];                                     // [ms, fn(dataview)]
const shots = {};
const at = (t, fn) => events.push([t, fn]);
const press = (id) => (d) => d.setUint32(8, d.getUint32(8, true) | 1 << id, true);
const turn = (enc, n) => (d) => d.setInt32(16 + 4 * enc, n, true);
const keys = (mask) => (d) => d.setUint32(0, mask, true);             // the note keys held (bit k = key k, F3 up)
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
    let p = 0, z = 0; for (let i = 0; i < a.length; i += 2) { p = Math.max(p, Math.abs(a[i])); if (i >= 2 && (a[i] < 0) !== (a[i - 2] < 0)) z++; }
    const half = Math.floor(ms / 500); peaks.set(half, Math.max(peaks.get(half) ?? 0, p));
    crossings.set(half, (crossings.get(half) ?? 0) + z);
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
// 0-4 s: it plays on its own. At 3 s the reverb return goes to zero so that a stopped sequencer is silent.
// 4-6 s: stopped, so screens can be compared.
at(3000, press(BTN.FX));                                                    // the FX page: send, decay, bright, return
at(3100, turn(ENC.K4, -20)); at(3150, press(BTN.HOME));
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
// lane 1 on COMPL (SEQ: the RANGE page; knob 3 is the chord follow) for two seconds, then back to OFF
at(12000, press(BTN.SEQ)); at(12050, turn(ENC.K3, 3)); at(12100, shot('compl')); at(14000, turn(ENC.K3, -3));
// a chord progression and a key change (GLO: HARMONY; knob 1 key, 3 chords)
at(14100, press(BTN.GLO)); at(14200, turn(ENC.K3, 2)); at(14300, turn(ENC.K1, 3));
at(17000, turn(ENC.K3, 4));                                                     // and on to WALK LR (progression 8)
// the FX, LFO and ENV buttons open their pages; an LFO on lane 1's chance keeps the music going
at(19000, press(BTN.FX)); at(19100, shot('fx'));
at(19200, press(BTN.LFO)); at(19300, shot('lfo')); at(19350, turn(ENC.K1, 1)); at(19400, turn(ENC.K3, 20));
at(19500, press(BTN.ENV)); at(19600, shot('env'));
// every Braids shape in turn (EDIT: SOUND; knob 1 is the shape)
at(20000, press(BTN.EDIT));
for (let i = 0; i < 65; i++) at(20100 + i * 145, turn(ENC.K1, 1));
// the reverb: send and return full up, play, stop, and the tail must ring on, then die away
at(30000, press(BTN.FX));
at(30100, turn(ENC.K1, 20)); at(30110, turn(ENC.K4, 20)); at(30200, press(BTN.HOME));
at(31500, press(BTN.PLAY));
// the delay: reverb return off, FX again is the DELAY page (1/8 note, full feedback and return); play, stop,
// and the echoes must ring on, then die away
at(38000, press(BTN.FX)); at(38100, turn(ENC.K4, -20)); at(38200, press(BTN.FX));
at(38300, turn(ENC.K1, -2)); at(38350, turn(ENC.K2, 20)); at(38400, turn(ENC.K4, 20)); at(38500, press(BTN.HOME));
at(38600, press(BTN.PLAY));
at(42000, press(BTN.PLAY));
// punch-in effects (REC: the PUNCH page; the keys are momentary effects): the delay return back down, play; BREAK (key 11,
// E4) held mutes every lane, let go brings them back; GATE (key 7) chops; leaving the page with HOME ends everything
at(47000, press(BTN.FX)); at(47100, turn(ENC.K4, -20)); at(47150, turn(ENC.K2, -20));   // FX returns to the DELAY page
at(47200, press(BTN.PLAY)); at(47300, press(BTN.REC)); at(47400, shot('punch'));
at(49500, keys(1 << 11)); at(49600, shot('punch held')); at(53500, keys(0));
at(56000, keys(1 << 7)); at(58500, keys(0)); at(58600, press(BTN.HOME));
// QUANT (ARP twice with nothing held): SCALE, then a chromatic run on the keys sounds and the page shows the setting
at(59000, press(BTN.ARP)); at(59100, press(BTN.ARP)); at(59200, turn(ENC.K1, 1)); at(59300, shot('quant'));
at(59400, keys(1 << 8)); at(60200, keys(1 << 9)); at(61000, keys(0)); at(61100, press(BTN.HOME));
// the per-voice filter (EDIT, EDIT: the FILTER page): lane 1's cutoff down to 10 for two seconds, then back up
at(61200, press(BTN.EDIT)); at(61300, press(BTN.EDIT)); at(61350, shot('filter')); at(61400, turn(ENC.K1, -45));
at(64400, turn(ENC.K1, 45)); at(64500, press(BTN.HOME));
const END = 67000;
events.sort((a, b) => a[0] - b[0]);
const inst = await WebAssembly.instantiate(mod, imports);
mem = inst.exports.memory; inp = inst.exports.web_in_ptr();
try { inst.exports.web_run(); } catch (e) { if (e.message !== 'done') throw e; }

const peak = (from, to) => Math.max(...[...peaks].filter(([h]) => h * 500 >= from && h * 500 < to).map(([, p]) => p), 0);
const changed = (a, b) => a.reduce((c, v, i) => c + (v !== b[i]), 0);
const ok = (name, cond) => { console.log((cond ? 'PASS ' : 'FAIL ') + name); if (!cond) process.exitCode = 1; };
const region = (f, y0, y1) => f.slice(y0 * 240, y1 * 240);
const row = (f, r) => region(f, 28 + r * 36, 28 + r * 36 + 34);   // HOME_ROW_Y in dinghy.c
const sameRows = (a, b, rows) => rows.every((r) => changed(row(a, r), row(b, r)) === 0);
const audible = (from, to) => { let n = 0, all = 0; for (let t = from; t < to; t += 500) { all++; if (peak(t, t + 500) > 200) n++; } return [n, all]; };
const patchName = (f) => {                       // the status bar after "U1 "
  const px = []; for (let y = 218; y < 240; y++) px.push(...f.slice(y * 240 + 24, y * 240 + 120)); return px;
};

ok('the startup screen draws Alfred and the title', changed(shots.boot, new Uint16Array(240 * 240)) > 3000);
ok('lanes make sound with no key pressed', peak(1000, 4000) > 1000);
ok('PLAY stops every note; only the reverb tail is left and it dies away', peak(5500, 6000) < 400 && peak(5500, 6000) < peak(4000, 4500));
const tail = [peak(32000, 32500), peak(33000, 33500), peak(36000, 36500)];
const echoes = [peak(42500, 43500), peak(44000, 45000), peak(46000, 47000)];
ok('the preset browser opens over the page', changed(shots['sound page'], shots['sound browser']) > 1500);
ok('SELECT in the browser chooses another family', changed(shots['sound browser'], shots.family) > 500);
ok('a button closes the browser', changed(shots['sound page'], shots['home 2']) > 0 && changed(shots.family, shots['home 2']) > 1500);
ok('the SOUND page shape knob changes the chosen lane only', changed(row(shots['home 2'], 0), row(shots['home shape'], 0)) > 0 &&
   sameRows(shots['home 2'], shots['home shape'], [1, 2, 3]));
ok('PRESETS on HOME opens the patch browser', changed(shots['home shape'], shots['patch browser']) > 1500);
ok('another patch changes every lane row', [0, 1, 2, 3].every((r) => changed(row(shots['home shape'], r), row(shots.patch, r)) > 0));
ok('a different slot looks different', changed(row(shots.patch, 1), row(shots.other, 1)) > 0);
ok('a saved patch loads back exactly', sameRows(shots.patch, shots.loaded, [0, 1, 2, 3]));
ok('the loaded slot is named after itself, not EMPTY', changed(patchName(shots.loaded), patchName(shots.other)) > 0 &&
   changed(patchName(shots.loaded), patchName(shots.patch)) > 0);
ok('PLAY starts it again', peak(6500, 7500) > 1000);
const algo = audible(6500, 12500);
ok(`every note algorithm keeps playing (${algo[0]} of ${algo[1]} half-seconds audible)`, algo[0] >= 0.75 * algo[1]);
const chords = audible(12500, 20000);
ok(`a chord progression keeps playing (${chords[0]} of ${chords[1]} half-seconds audible)`, chords[0] >= 0.75 * chords[1]);
const shapes = audible(20500, 29500);
ok(`every shape plays without crashing the firmware (${shapes[0]} of ${shapes[1]} half-seconds audible)`, shapes[0] >= 0.8 * shapes[1]);
ok(`the reverb tail rings on after PLAY stops and then dies away (${tail.join(', ')})`, tail[0] > 300 && tail[1] < tail[0] && tail[2] <= tail[1]);
ok(`the delay echoes ring on after PLAY stops and then die away (${echoes.join(', ')})`,
  echoes[0] > 300 && echoes[1] < echoes[0] && echoes[2] < echoes[1]);
ok('FX, LFO and ENV open three different pages', changed(shots.fx, shots.lfo) > 500 && changed(shots.lfo, shots.env) > 500 && changed(shots.fx, shots.env) > 500);
ok('REC opens the PUNCH page and a held key lights its cell', changed(shots.punch, shots['home 2']) > 1500 && changed(shots.punch, shots['punch held']) > 100);
const before = peak(48000, 49500), muted = peak(52000, 53400), after = peak(54500, 56000), gated = peak(56500, 58500), left = peak(58600, 59000) || peak(59400, 61000);
ok(`BREAK held mutes every lane and letting go brings them back (${before}, ${muted}, ${after})`, before > 1000 && muted < before / 4 && after > 1000);
ok(`GATE chops the mix and HOME ends the punch-ins (${gated}, ${left})`, gated > 500 && left > 1000);
ok('ARP twice with nothing held is the QUANT page', changed(shots.quant, shots.punch) > 500 && changed(shots.quant, shots['home 2']) > 500);
const zc = (from, to) => { let n = 0; for (let t = from; t < to; t += 500) n += crossings.get(t / 500) ?? 0; return n; };
const bright = zc(59500, 61000), dark = zc(62000, 64000), back = zc(65000, 67000);
ok(`the FILTER page's cutoff darkens lane 1 and lets it back (zero crossings ${bright}, ${dark}, ${back})`,
   changed(shots.filter, shots['sound page']) > 300 && dark < bright * 0.75 && back > dark);
const scaleMask = inst.exports.web_harmony_mask;
const bits = (m) => m.toString(2).split('1').length - 1;
ok('the scales are real: minor in C is 0x5AD, major in D is major turned up two semitones, a triad has three notes',
   scaleMask(1, 0, 0, 0, 0) === 0x5AD && scaleMask(0, 2, 0, 0, 0) === (((0xAB5 << 2) | (0xAB5 >> 10)) & 0xFFF) &&
   bits(scaleMask(0, 0, 1, 0, 2)) === 3);
ok('COMPL is the notes outside the key: C major gives the black keys, the chromatic scale stays whole',
   scaleMask(0, 0, 0, 0, 3) === (0xFFF ^ 0xAB5) && scaleMask(7, 0, 0, 0, 3) === 0xFFF);
// the L R walk from C major: C, E minor, G, B minor (progression 8; TRIAD follow); every chord shares two notes with the last
const triad = (s) => scaleMask(0, 0, 8, s, 2);
ok('WALK LR from C major goes C, Em, G, Bm, a triad each, two notes in common each move',
   triad(0) === 0x091 && triad(1) === 0x890 && triad(2) === 0x884 && triad(3) === 0x844 &&
   [0, 1, 2, 3, 22].every((s) => bits(triad(s)) === 3 && bits(triad(s) & triad(s + 1)) === 2));
ok('the RANGE page shows COMPL', changed(shots.compl, shots['home 2']) > 500);
ok('no Lean runtime reports', reports.length === 0);
// the proofs, watched (fw/firmware/src/watch.h): the theorems' statements checked on the running machine
const watched = [];
for (let i = 0; i < inst.exports.web_watch_count(); i++) {
  const b = new Uint8Array(mem.buffer, inst.exports.web_watch_name(i)); let n = 0; while (b[n]) n++;
  watched.push([Buffer.from(b.subarray(0, n)).toString(), inst.exports.web_watch_checks(i), inst.exports.web_watch_fails(i)]);
}
const idle = watched.filter(([, c]) => c === 0).map(([t]) => t), broken = watched.filter(([, , f]) => f > 0).map(([t, c, f]) => `${t} ${f}/${c}`);
const checks = watched.reduce((a, [, c]) => a + c, 0);
ok(`every watched theorem was checked on the running machine (${watched.length} theorems, ${checks} checks)${idle.length ? ': never checked ' + idle.join(' ') : ''}`, idle.length === 0);
ok(`no watched theorem failed${broken.length ? ': ' + broken.join(', ') : ''}`, broken.length === 0);
const leanPoolUsed = inst.exports.web_lean_pool_used();
ok(`the Lean heap's high-water mark stays under half its 32 KiB pool (${leanPoolUsed} B)`, leanPoolUsed < 16384);
console.log({ reports });
console.log(watched.map(([t, c, f]) => `${t}:${c}/${f}`).join(" "));
if (process.env.PEAKS) console.log([...peaks].map(([h, p]) => `${h * 0.5}s:${p}`).join(' '));
