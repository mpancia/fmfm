# Effects

Two sends on one bus: each lane's SEND (on the REVERB page) feeds both the reverb and the delay; each effect has
its own RETURN. The FX button opens REVERB, and again DELAY.

## Reverb send

A stereo reverb on a send bus: each lane sends some of its sound to it, the reverb adds its wet signal to the mix.
It is the reverb of Clouds (Mutable Instruments, MIT, Emilie Gillet), ported to fixed-point with its arithmetic
in Lean.

| Control (FX button, then knobs) | Does |
|---|---|
| SEND | how much of the chosen lane goes to the reverb (0 to 100%, kept in the patch) |
| DECAY | how long the tail rings (0 to 100%; the loop gain runs from 0.35 to 0.98) |
| BRIGHT | how dark or bright the tail is (the low-pass in each loop, 0.6 to 0.97) |
| RETURN | how loud the wet signal is in the mix (0 to 100%; 100% is a gain of 1.0) |

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

See `docs/PROOFS.md`, section Reverb, eleven theorems:

- every position is inside the memory; at every scale up to 400 the ten delay lines fit and never overlap;
- the two modulated reads (the first diffuser and the long delay of the second loop) stay inside their own line
  whatever the LFO does, at every scale from 192 to 400, and the LFO's wobble is always between 0 and 1.0;
- every decay and brightness setting gives a gain below 1.0, and a signal times a gain of at most 1.0 keeps its sign
  and never grows, rounding included;
- one step of the low-pass lands between its state and its input, and an interpolated read lands between its two
  neighbours, so neither can overshoot;
- the stored sample saturates instead of wrapping;
- one trip round the two loops with nothing coming in scales a sample by the decay gain squared, plus at most
  one unit of rounding, so an undriven tail shrinks every trip (`reverb_round_trip_decays`);
- the wet sample handed to the mix is within 2^29 + 2^21 and its return at any RETURN setting is exact
  (`reverb_wet_never_overflows`); `mix_bus_never_wraps` takes exactly that bound, so the two promises join.

These last two are about `Spec/Reverb.lean`, which writes down the glue's sequence of calls for one sample
with the memory reads as parameters. That the spec is the glue is checked, not assumed: `make test-lean`
runs `tests/reverb_spec_diff.c`, which records what the glue reads before each of 20000 samples (a burst,
a settings change, the tail) and `tests/reverb_spec.lean` recomputes both outputs from the spec; they agree
on every sample, and swapping two reads in the spec makes 18342 of them disagree.

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

### Levels

Measured with `tools/render_web.mjs` (the simulator's output as a WAV, with its loudness by the second):

- INIT at its defaults (sends 15 to 45%, return 70%): the wet signal is 12.6 dB under the dry mix.
- DECAY 0 dies within a second of PLAY stopping; DECAY 50 falls about 13 dB a second (RT60 near 4 s);
  DECAY 100 (loop gain 0.98) is a wash that keeps building while the lanes play, as it does in Clouds.
- The worst case, every send, DECAY and RETURN at 100% for 30 s, reaches -10 dBFS RMS and clips 45 samples.
  With a return of 2.0 it clipped 3.7% of its samples, which is why 100% is now a gain of 1.0.
- All 121 factory patches, 9 s each: peaks from -17 to -2.2 dBFS, no clipping, none silent.

### Not done, not measured

- Not heard: the numbers say the port follows Clouds and that nothing clips, not that it sounds good.
- Not measured on the chip: about 720 chip instructions a sample (`docs/BUDGET.md`), the price of two INIT
  patches' voices. The memory is 64 KiB of the pool (the pool use is 267 KiB of 344 KiB).
- No delay, no chorus, no other Clouds parts (granular, pitch shifter, diffuser). The diffuser inside the reverb is
  part of it.

## Delay send

A tempo-synced echo on the same send bus: one line of 32768 16-bit samples (743 ms at 44.1 kHz), read a note value
behind the write position and fed back through a low-pass. The arithmetic is `Firmware/Delay.lean` (it reuses the
reverb's `mul` and `lowpass`); the line is `fx/delay_glue.c`.

| Control (FX, FX, then knobs) | Does |
|---|---|
| TIME | the note value of the echo: 1/32, 1/16, 1/8T, 1/16., 1/8, 1/4T, 1/8., 1/4 of the tempo |
| FEEDBK | how much of each echo goes round again (0 to 100%; 100% is a gain of 0.95) |
| TONE | the low-pass in the loop (0.2 to 1.0; 100% is no filtering) |
| RETURN | how loud the echo is in the mix (0 to 100%; 100% is unity) |

The four belong to the patch (layout version 3, 102 bytes); the echo follows the TEMPO knob and a patch's tempo,
retuning whenever the tempo changes. Notes longer than the line allows at a slow tempo are held at 743 ms (a
quarter note below 81 bpm, a dotted eighth below 61). With RETURN at 0 the delay does not run, and when it comes
back the old echoes are dropped.

What is proved (`docs/PROOFS.md`, section Delay): the feedback gain is at most 0.95 and the tone between 0.2 and
1.0 for every setting; with nothing new on the send, what goes back into the line is at most 95% of the echo plus
one count of rounding, so a tail of echoes shrinks geometrically whatever the settings; the delay in samples is
always between 1 and 32767, so the line never reads where it writes; note values up to a dotted sixteenth are exact
at every tempo from 40 to 240; a send louder than full scale saturates in the line instead of wrapping. The patch
round-trip proofs cover the four new bytes.

Tested: `make test` plays with the delay at full feedback and return, stops, and checks that the echoes ring on and
die away. Rendered with `tools/render_web.mjs` at 64 bpm and a dotted eighth, the peaks after a stop come every
0.7 s, as they should (703 ms). Not heard. Cost: about 85 host instructions a sample (`make perf`), a seventh of the reverb. Memory:
64 KiB of the pool, which is now 333 KiB of 344 KiB.
