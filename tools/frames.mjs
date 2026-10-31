// Run a firmware wasm headless and save the screen at the given times as raw RGB565 files.
//   node tools/frames.mjs build/web/dinghy.wasm OUT_DIR 300,1000,2000
// Optional script of panel input: ... 300,1000 "4000:press:7,4500:turn:5:1"  (ms:press:button, ms:turn:encoder:detents)
import fs from 'fs';
const [wasm, outDir, times, script = ''] = process.argv.slice(2);
const wanted = times.split(',').map(Number);
const input = script.split(',').filter(Boolean).map((e) => e.split(':'));
const mod = await WebAssembly.compile(fs.readFileSync(wasm));
let mem, inp, ms = 0, frame = Buffer.alloc(240 * 240 * 2);
const imports = { env: {
  js_sync(t) {
    ms = t;
    const d = new DataView(mem.buffer, inp);
    for (const [at, kind, a, b] of input) if (Number(at) === t) {
      if (kind === 'press') d.setUint32(8, d.getUint32(8, true) | 1 << Number(a), true);
      if (kind === 'turn') d.setInt32(16 + 4 * Number(a), Number(b), true);
    }
    if (wanted.includes(t)) fs.writeFileSync(`${outDir}/${t}.raw`, frame);
    if (t > Math.max(...wanted)) throw new Error('done');
  },
  js_audio() {},
  js_frame(ptr) { frame = Buffer.from(mem.buffer.slice(ptr, ptr + 240 * 240 * 2)); },
  js_report() {},
} };
fs.mkdirSync(outDir, { recursive: true });
const inst = await WebAssembly.instantiate(mod, imports);
mem = inst.exports.memory; inp = inst.exports.web_in_ptr();
try { inst.exports.web_run(); } catch (e) { if (e.message !== 'done') throw e; }
