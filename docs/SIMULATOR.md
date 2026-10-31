# Web simulator

`make run` builds and serves it; `make web` only builds into `build/web/`; `make test` runs it headless in node.

## What runs
The same `fw/firmware/src/dinghy.c` that goes on the chip, compiled with `-DDINGHY_WEB` to WebAssembly by the
clang and lld inside the pinned Lean toolchain (`tools/build_web.sh`), together with the Lean code in `Firmware/`
and its runtime (`rt/`). No emscripten, no libc.
`web/web_host.c` plays the part of the hardware (derived from Dinghy's `tests/host.c`): screen buffer, inputs,
RAM-backed settings, MIDI queue.

```
page (sim.js)  --SharedArrayBuffer-->  worker.js  (runs the wasm; app_main never returns)
                                         |  js_audio: 256-frame blocks      js_frame: screen + LEDs
                                         v
                              AudioWorklet (worklet.js) plays the ring buffer
```
`platform_poll()` is one simulated millisecond. It calls `js_sync`, which loads the page's input and
sleeps while the audio buffer is full, so the audio clock sets the speed. Pages need `SharedArrayBuffer`, which
needs the two headers `tools/serve_web.py` sends; opening `build/web/index.html` from disk will not work.

## Controls
Click the keys, or use the computer keyboard (`Z`..`/` from C4, `Q`..`T` from C5; `-`/`=` are OCT-/OCT+).
Knobs: wheel, drag, click left/right half, arrow keys. **Connect MIDI in** feeds Web MIDI devices to the USB
MIDI input (Chrome/Edge).

## What it does not model
- CPU time: the chip is far slower than your computer. Check the audio ISR budget on hardware (`fm1_ticks()`), or
  by comparing instruction counts in a build for the chip.
- Flash: settings live in RAM and vanish at power off. No update path, rescue or boot guard.
- TRS MIDI, MIDI out, USB audio device behaviour, key scan timing, battery.
- Hardware rules (no float, no 64-bit division, ROM window addresses) are enforced only by `make fw`, not here.
  Always run `make fw` before flashing.
