// Every factory patch, played for a few seconds in the web build (run by `make test`): none may clip, none
// may be silent, and the Lean runtime must not report. Loads each patch the way the simulator page's list does
// (the `patch` field of web_in) and measures the audio the firmware hands to the page.
//   node tools/check_patches.mjs [seconds per patch, default 6]
import fs from 'fs';
const mod = await WebAssembly.compile(fs.readFileSync(process.env.WASM || 'build/web/dinghy.wasm'));
const SECONDS = Number(process.argv[2] || 6);
let mem, inp, ms = 0, count = 0, current = -1, reports = [];
const stats = [];                                      // per patch: { peak, clipped, loud (samples over 1000) }
const imports = { env: {
  js_sync(t) {
    ms = t;
    const d = new DataView(mem.buffer, inp);
    if (t === 800) d.setUint32(8, 1 << 8, true);       // HOME skips the startup screen
    const slot = Math.floor((t - 1000) / (SECONDS * 1000));
    if (t >= 1000 && (t - 1000) % (SECONDS * 1000) === 0) {
      if (slot >= count) throw new Error('done');
      d.setUint32(112, slot + 1, true);                // load patch `slot`
      current = slot; stats[slot] = { peak: 0, clipped: 0, loud: 0 };
    }
  },
  js_audio(ptr, n) {
    if (current < 0 || (ms - 1000) % (SECONDS * 1000) < 1500) return;   // skip the first 1.5 s: the load, the old tail
    const a = new Int16Array(mem.buffer, ptr, n * 2), s = stats[current];
    for (const v of a) {
      const m = Math.abs(v);
      if (m > s.peak) s.peak = m;
      if (v >= 32767 || v <= -32768) s.clipped++;
      if (m > 1000) s.loud++;
    }
  },
  js_frame() {},
  js_report(ptr, fatal) {
    const b = new Uint8Array(mem.buffer, ptr); let n = 0; while (b[n]) n++;
    reports.push((fatal ? 'FATAL ' : '') + Buffer.from(b.subarray(0, n)).toString());
  },
} };
const inst = await WebAssembly.instantiate(mod, imports);
mem = inst.exports.memory; inp = inst.exports.web_in_ptr();
count = inst.exports.web_patch_count();
const names = [];
for (let i = 0; i < count; i++) {
  const b = new Uint8Array(mem.buffer, inst.exports.web_patch_name(i)); let n = 0; while (b[n]) n++;
  names.push(Buffer.from(b.subarray(0, n)).toString());
}
try { inst.exports.web_run(); } catch (e) { if (e.message !== 'done') throw e; }

let bad = 0;
const factory = stats.filter((s, i) => !names[i].startsWith('USER'));
factory.forEach((s, i) => {
  const problems = [];
  if (s.clipped > 0) problems.push(`${s.clipped} clipped samples`);
  if (s.loud < 44100 * 0.5) problems.push(`nearly silent (${s.loud} samples over 1000)`);
  if (problems.length) { bad++; console.log(`FAIL ${names[i]}: ${problems.join(', ')} (peak ${s.peak})`); }
});
const peaks = factory.map((s) => s.peak);
console.log(`${bad ? 'FAIL' : 'PASS'} ${factory.length} factory patches, ${SECONDS} s each: ${bad} with clipping or silence; ` +
  `peaks ${Math.min(...peaks)} to ${Math.max(...peaks)}`);
if (reports.length) { bad++; console.log('FAIL Lean runtime reports:', reports); }
process.exitCode = bad ? 1 : 0;
