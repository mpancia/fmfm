/* Runs the firmware (dinghy.wasm). app_main never returns, so this worker lives inside web_run():
 * js_sync (called once per simulated millisecond) reads the player's input and, when the audio ring is full,
 * sleeps until the AudioWorklet has drained some. Audio is the clock. Layout of `ctl`: see sim.js. */
'use strict';
const RING = 16384, TARGET = 2048;          // frames; ring must be a power of two
let ctl, ring, frame, mem, inp, exports, wrote = 0;

const imports = { env: {
  js_sync(ms) {
    for (;;) {                               // wait while the listener has plenty queued
      const r = Atomics.load(ctl, 14);
      if (((wrote - r) | 0) < TARGET) break;
      Atomics.wait(ctl, 14, r, 2);
    }
    const dv = new DataView(mem.buffer, inp);
    dv.setUint32(0, Atomics.load(ctl, 0), true);               // notes held
    dv.setUint32(4, Atomics.load(ctl, 1), true);               // buttons held
    dv.setUint32(8, Atomics.exchange(ctl, 2, 0), true);        // button press edges
    dv.setUint32(12, Atomics.exchange(ctl, 3, 0), true);       // button release edges
    for (let i = 0; i < 7; i++) dv.setInt32(16 + 4 * i, Atomics.exchange(ctl, 4 + i, 0), true);
    let n = 0, mr = Atomics.load(ctl, 12);
    const mw = Atomics.load(ctl, 11);
    while (mr !== mw && n < 16) {                              // MIDI in
      const m = Atomics.load(ctl, 32 + (mr & 63));
      dv.setUint8(48 + 4 * n, m & 255); dv.setUint8(49 + 4 * n, (m >> 8) & 255);
      dv.setUint8(50 + 4 * n, (m >> 16) & 255); dv.setUint8(51 + 4 * n, (m >>> 24) & 255);
      mr = (mr + 1) | 0; n++;
    }
    Atomics.store(ctl, 12, mr);
    dv.setUint32(44, n, true);
    dv.setUint32(112, Atomics.exchange(ctl, 20, 0), true);     // a patch to load (index + 1)
    dv.setUint32(116, Atomics.exchange(ctl, 22, 0), true);     // the Demo button: 1 start, 2 stop
    Atomics.store(ctl, 21, exports.web_patch_index());
    Atomics.store(ctl, 23, exports.web_demo_auto());
    Atomics.store(ctl, 19, ms);
    if (ms % 500 === 0) {                                      // the watched theorems' counters (watch.h), twice a second
      const watch = [];
      for (let i = 0; i < exports.web_watch_count(); i++) {
        const b = new Uint8Array(mem.buffer, exports.web_watch_name(i)); let n = 0; while (b[n]) n++;
        watch.push([new TextDecoder().decode(b.subarray(0, n)), exports.web_watch_checks(i), exports.web_watch_fails(i)]);
      }
      postMessage({ watch });
    }
  },
  js_audio(ptr, frames) {
    const src = new Int16Array(mem.buffer, ptr, frames * 2);
    const at = (wrote & (RING - 1)) * 2;
    ring.set(src, at);                       // blocks are 256 frames and RING is a multiple: never wraps mid-block
    wrote = (wrote + frames) | 0;
    Atomics.store(ctl, 13, wrote);
  },
  js_report(ptr, fatal) {                    // a message from the Lean runtime
    const b = new Uint8Array(mem.buffer, ptr); let n = 0; while (b[n]) n++;
    postMessage({ report: new TextDecoder().decode(b.subarray(0, n)), fatal });
  },
  js_frame(ptr, lo, hi) {
    frame.set(new Uint16Array(mem.buffer, ptr, 240 * 240));
    Atomics.store(ctl, 15, lo); Atomics.store(ctl, 16, hi);
    Atomics.add(ctl, 17, 1);
  },
} };

onmessage = async (e) => {
  ctl = new Int32Array(e.data.ctl); ring = new Int16Array(e.data.ring); frame = new Uint16Array(e.data.frame);
  try {
    const { instance } = await WebAssembly.instantiateStreaming(fetch(new URL('dinghy.wasm', e.data.base)), imports);
    exports = instance.exports;
    mem = exports.memory; inp = exports.web_in_ptr();
    const patches = [];                      // the patch names, read before the firmware starts
    for (let i = 0; i < exports.web_patch_count(); i++) {
      const b = new Uint8Array(mem.buffer, exports.web_patch_name(i)); let n = 0; while (b[n]) n++;
      patches.push(new TextDecoder().decode(b.subarray(0, n)));
    }
    postMessage({ ready: true, patches });
    instance.exports.web_run();
  } catch (err) { postMessage({ error: String(err && err.message || err) }); }
};
