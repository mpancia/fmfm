# Web simulator

`make run` builds and serves it; `make web` only builds into `build/web/`; `make test` runs it headless in node.

## What runs
The same `fw/firmware/src/dinghy.c` that goes on the chip, compiled with `-DDINGHY_WEB` to WebAssembly by the
clang and lld in the pinned Lean toolchain (`tools/build_web.sh`), with the Lean code in `Firmware/` and its
runtime (`rt/`). No emscripten, no libc.
`web/web_host.c` stands in for the hardware (from Dinghy's `tests/host.c`): screen buffer, inputs, RAM-backed
settings, MIDI queues in and out.

```
page (sim.js)  --SharedArrayBuffer-->  worker.js  (runs the wasm; app_main never returns)
                                         |  js_audio: 256-frame blocks      js_frame: screen + LEDs
                                         v
                              AudioWorklet (worklet.js) plays the ring buffer
```
`platform_poll()` is one simulated millisecond. It calls `js_sync`, which loads the page's input and sleeps while
the audio buffer is full, so the audio clock sets the speed. Pages need `SharedArrayBuffer`, which needs the two
headers `tools/serve_web.py` sends; opening `build/web/index.html` from disk does not work.

## Controls
Click the keys, or use the computer keyboard (`Z`..`/` from C4, `Q`..`T` from C5; `-`/`=` are OCT-/OCT+). Space is
PLAY, Escape is HOME, `[` and `]` turn Select, PageUp and PageDown step through the patches.
Knobs: wheel, drag, click left/right half, arrow keys. Every button and knob has a tooltip.
**Record** saves what you hear as a WebM (Opus) file; **Screenshot** saves the 240x240 screen as a PNG; **Copy link**
puts `?patch=N` on the URL, and opening such a link loads that patch after Power on. **Connect MIDI** (Chrome/Edge)
feeds every Web MIDI input to the firmware's USB MIDI in and shows a list of outputs; the chosen one gets what the
firmware sends (the lanes on MIDI OUT CH, the keys on channel 16), with All Notes Off when the output changes or the
device powers off. The **Patch** list loads any factory patch or user slot without touching the device
(the page asks the firmware for the names at boot and follows the patch the device changes to). **Demo** turns
AUTO on (GLO > BANKS) and the demo songs play themselves; from power-off it boots first. Press it again, or PLAY,
to stop.
**Tour** is a guided walk of about eighty seconds for someone who has never seen the panel: the page loads the
boot patch, presses the buttons and turns the knobs itself (HOME, the SEQ pages, HARMONY, SOUND, FILTER, REVERB,
PUNCH, HOME) and a caption under the device says what the screen shows. Press it again, or any key, button or
knob, to stop; it ends by loading the boot patch again. The page keeps the firmware's page-per-group memory
(`goto_group` in `dinghy.c`) in step with every press, so a tour run from any page lands where its captions say.

## What it does not model
- CPU time: the chip is far slower than your computer. Check the audio ISR budget on hardware (`fm1_ticks()`) or
  by comparing instruction counts in a build for the chip.
- Flash: settings live in RAM and vanish at power off. No update path, rescue or boot guard.
- TRS MIDI, USB audio device behaviour, key scan timing, battery.
- Hardware rules (no float, no 64-bit division, ROM window addresses) are enforced only by `make fw`. Run
  `make fw` before flashing.
