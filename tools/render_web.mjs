// Run a firmware wasm headless and write what it plays as a stereo 16-bit WAV, with a few numbers about it.
//   node tools/render_web.mjs build/web/dinghy.wasm out.wav 12000 "800:press:8,3000:press:2,3100:turn:5:-20"
// The script is as for frames.mjs (ms:press:button, ms:turn:encoder:detents, ms:key:k:1 or :0 to hold or let go of
// key k, 0 = F3). Prints the peak, the loudness
// (RMS, dBFS) of each second and how many samples clipped.
import fs from 'fs';
const [wasm, out, lengthMs, script = ''] = process.argv.slice(2);
const END = Number(lengthMs);
const input = script.split(',').filter(Boolean).map((e) => e.split(':'));
const mod = await WebAssembly.compile(fs.readFileSync(wasm));
let mem, inp, ms = 0;
const chunks = [];
const imports = { env: {
  js_sync(t) {
    ms = t;
    const d = new DataView(mem.buffer, inp);
    for (const [at, kind, a, b] of input) if (Number(at) === t) {
      if (kind === 'press') d.setUint32(8, d.getUint32(8, true) | 1 << Number(a), true);
      if (kind === 'turn') d.setInt32(16 + 4 * Number(a), Number(b), true);
      if (kind === 'key') d.setUint32(0, Number(b) ? d.getUint32(0, true) | 1 << Number(a) : d.getUint32(0, true) & ~(1 << Number(a)), true);
    }
    if (t >= END) throw new Error('done');
  },
  js_audio(ptr, n) { chunks.push(new Int16Array(mem.buffer.slice(ptr, ptr + n * 4))); },
  js_frame() {},
  js_report(ptr, fatal) {
    const b = new Uint8Array(mem.buffer, ptr); let n = 0; while (b[n]) n++;
    console.error((fatal ? 'FATAL ' : '') + Buffer.from(b.subarray(0, n)).toString());
  },
} };
const inst = await WebAssembly.instantiate(mod, imports);
mem = inst.exports.memory; inp = inst.exports.web_in_ptr();
try { inst.exports.web_run(); } catch (e) { if (e.message !== 'done') throw e; }

const frames = chunks.reduce((n, c) => n + c.length / 2, 0);
const pcm = new Int16Array(frames * 2);
let at = 0; for (const c of chunks) { pcm.set(c, at); at += c.length; }
const RATE = 44100;
const header = Buffer.alloc(44);
header.write('RIFF', 0); header.writeUInt32LE(36 + pcm.byteLength, 4); header.write('WAVE', 8);
header.write('fmt ', 12); header.writeUInt32LE(16, 16); header.writeUInt16LE(1, 20); header.writeUInt16LE(2, 22);
header.writeUInt32LE(RATE, 24); header.writeUInt32LE(RATE * 4, 28); header.writeUInt16LE(4, 32); header.writeUInt16LE(16, 34);
header.write('data', 36); header.writeUInt32LE(pcm.byteLength, 40);
fs.writeFileSync(out, Buffer.concat([header, Buffer.from(pcm.buffer)]));

let peak = 0, clipped = 0;
const seconds = [];
for (let s = 0; s * RATE < frames; s++) {
  let sum = 0, n = 0;
  for (let i = s * RATE * 2; i < Math.min((s + 1) * RATE, frames) * 2; i++) {
    const v = pcm[i]; sum += v * v; n++;
    if (Math.abs(v) > peak) peak = Math.abs(v);
    if (v >= 32767 || v <= -32768) clipped++;
  }
  seconds.push(n ? 20 * Math.log10(Math.sqrt(sum / n) / 32768 + 1e-9) : -180);
}
console.log(`${out}: ${(frames / RATE).toFixed(1)} s, peak ${peak} (${(20 * Math.log10(peak / 32768 + 1e-9)).toFixed(1)} dBFS), ` +
  `${clipped} clipped samples`);
console.log('dBFS by second: ' + seconds.map((v) => v.toFixed(0)).join(' '));
{                                            // the watched theorems (fw/firmware/src/watch.h): checks and failures
  const w = []; let fails = 0, checks = 0;
  for (let i = 0; i < inst.exports.web_watch_count(); i++) {
    const b = new Uint8Array(inst.exports.memory.buffer, inst.exports.web_watch_name(i)); let n = 0; while (b[n]) n++;
    const c = inst.exports.web_watch_checks(i), f = inst.exports.web_watch_fails(i);
    checks += c; fails += f; if (f) w.push(`${Buffer.from(b.subarray(0, n))} ${f}/${c}`);
  }
  console.log(`watched: ${checks} checks, ${fails} failed${w.length ? ' (' + w.join(', ') + ')' : ''}`);
}
