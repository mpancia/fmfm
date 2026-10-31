# Effects

## Reverb send

A stereo reverb on a send bus: each lane sends some of its sound to it, the reverb adds its wet signal to the mix.
It is the reverb of Clouds (Mutable Instruments, MIT, Emilie Gillet), ported to fixed-point with its arithmetic
in Lean.

| Control (FX button, then knobs) | Does |
|---|---|
| SEND | how much of the chosen lane goes to the reverb (0 to 100%, kept in the patch) |
| DECAY | how long the tail rings (0 to 100%; the loop gain runs from 0.35 to 0.98) |
| BRIGHT | how dark or bright the tail is (the low-pass in each loop, 0.6 to 0.97) |
| RETURN | how loud the wet signal is in the mix (0 to 100%; 100% is a gain of 2.0) |

DECAY, BRIGHT and RETURN belong to the patch; SEND belongs to each lane. With RETURN at 0 the reverb does not run at
all (it costs nothing), and when it comes back on the old tail is dropped.

### The network

Clouds' reverb is the Griesinger topology from Dattorro's paper. The send goes through four allpass diffusers; the
result feeds two loops, each two allpasses and a long delay, crossed so each loop feeds the other, with a low-pass in
each. Two slow LFOs (0.5 Hz and 0.3 Hz) move the read position of one diffuser and of the long delay of the first
loop, so the tail shimmers instead of ringing at fixed frequencies. The left and right outputs are the two loops.

Delay lines are Clouds' sizes scaled by 353/256 from its 32 kHz to our 44.1 kHz, so the room is the same size. They
live in one 32768-sample memory, stored as 16 bits holding the signal times 4096 (Clouds' 12-bit format).

### How it is built

```
Firmware/Reverb.lean      the arithmetic of one sample: scalar functions (positions, saturating store, gain, low-pass,
                          interpolation, LFO, parameter maps)
Firmware/ReverbApi.lean   one C entry per function
fx/reverb_glue.c          the delay memory, the write position, the filter states, and the network in Clouds' order
fx/reverb.h               the C interface
```

As for the engines (`docs/LEAN-ENGINES.md`), Lean's generated C is included in the glue as inline functions, so the
audio interrupt runs plain integer code with no Lean runtime. The order of operations in the network is C, copied
from `Reverb::Process`; the arithmetic of each step is Lean.

### What is proved

See `docs/PROOFS.md`, section Reverb, nine theorems:

- every position is inside the memory; at every scale up to 400 the ten delay lines fit and never overlap;
- the two modulated reads (the first diffuser and the long delay of the second loop) stay inside their own line
  whatever the LFO does, at every scale from 192 to 400, and the LFO's wobble is always between 0 and 1.0;
- every decay and brightness setting gives a gain below 1.0, and a signal times a gain of at most 1.0 keeps its sign
  and never grows, rounding included;
- one step of the low-pass lands between its state and its input, and an interpolated read lands between its two
  neighbours, so neither can overshoot;
- the stored sample saturates instead of wrapping.

Not proved: that the whole network is stable. Each step is shown not to grow a sample on its own, but the allpasses
add a delayed sample to a scaled one, and the two loops feed each other; the gain budget is Clouds' design and what
the test shows is that the tail dies away.

### How it is tested

`make test-lean` runs `tests/reverb_diff.cc`: the same input and settings through Clouds' original float code
(`tests/reference/clouds`, unchanged, namespace renamed at compile time) and through the port, at Clouds' own sizes.

- For the first 4000 samples, before the long delays are first read, the two agree to within -41 dB (a click) of
  rounding error.
- After that the LFO matters: the port's sine is a parabola and Clouds' is a recurrence, so a delay time differs by a
  tenth of a sample and the wobbling tails are not the same waveform. The tail is compared by loudness in 50 ms
  windows, down to -41 dBFS: the worst window is within 1.04 dB of the original, the mean within 0.4 dB, over five
  inputs (clicks at three settings, a noise burst, a sine burst).
- `make test` checks in the simulator that the tail rings on after PLAY stops and then dies away.

### Not done, not measured

- Not heard: the numbers say the port follows Clouds, not that the settings are good.
- Not measured on the chip: the cost is about 20 multiplies per sample per channel, plus the voices. The memory is
  64 KiB of the pool (the pool use is 267 KiB of 344 KiB).
- No delay, no chorus, no other Clouds parts (granular, pitch shifter, diffuser). The diffuser inside the reverb is
  part of it.
