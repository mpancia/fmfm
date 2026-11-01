// Every demo song rendered headless (GLO > BANKS, the DEMO knob) and held to a band: no clipped sample, a peak
// between -20 and -3 dBFS, a loudness over the whole render between -36 and -20 dBFS (so the demos sit near one another), and no Lean runtime report.
//   node tools/smoke_demos.mjs build/web/dinghy.wasm
import fs from 'fs';
import { execFileSync } from 'child_process';
const wasm = process.argv[2] ?? 'build/web/dinghy.wasm';
const src = fs.readFileSync('voices/presets.h', 'utf8');
const ndemo = Number(src.match(/#define NDEMO (\d+)u/)[1]);
const names = [...src.matchAll(/^    \{"([^"]+)", /gm)].map((m) => m[1]).slice(-Number(src.match(/#define NPATCHES (\d+)u/)[1]), -Number(src.match(/#define NPATCHES (\d+)u/)[1]) + ndemo);
let failed = 0;
const ok = (name, cond) => { console.log((cond ? 'PASS ' : 'FAIL ') + name); if (!cond) failed++; };
for (let i = 0; i < ndemo; i++) {
  // skip the startup screen, four GLO presses to BANKS, the DEMO knob to demo i, then 16 s of it
  const script = `800:press:8,2000:press:7,2100:press:7,2200:press:7,2300:press:7,2400:turn:4:${i}`;
  const out = `build/demo_${i}.wav`;
  let text;
  try {
    text = execFileSync('node', ['tools/render_web.mjs', wasm, out, '19000', script], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] });
  } catch (e) { ok(`${names[i]} renders`, false); console.log(String(e.stderr).split('\n').slice(0, 3).join('\n')); continue; }
  const peak = Number(text.match(/peak \d+ \((-?[\d.]+) dBFS\)/)[1]);
  const clipped = Number(text.match(/(\d+) clipped/)[1]);
  const seconds = text.match(/dBFS by second: (.*)/)[1].trim().split(' ').map(Number).slice(3);   // after the demo loads
  const loud = 10 * Math.log10(seconds.reduce((s, v) => s + Math.pow(10, v / 10), 0) / seconds.length);
  ok(`${names[i]}: no clipping, peak ${peak} dBFS in -20..-3, loudness ${loud.toFixed(1)} dBFS in -36..-20`,
    clipped === 0 && peak >= -20 && peak <= -3 && loud > -36 && loud < -20);
}
process.exitCode = failed ? 1 : 0;
