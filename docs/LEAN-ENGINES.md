# Braids engines in Lean

The sound engines are Mutable Instruments' Braids. They are being ported from C++ to Lean one at a time. A ported
engine is Lean that the firmware runs and that is checked against the original two ways: it must produce the same
samples, and the arithmetic has proofs.

## How a port is built

```
Firmware/Analog.lean       the arithmetic of one sample: pure scalar functions (UInt32, Int32, Int16)
Firmware/AnalogApi.lean    one export per result field, so every call returns a plain number
        |  lake: Lean -> C
voices/analog_glue.c       includes that C as inline functions; owns the buffers and the sample loop
voices/braids/analog_oscillator.cc   the C++ class calls the glue; everything not yet ported is still C++
```

Lean cannot allocate in the audio interrupt, so engine code is scalar only: no `Array`, no structures that survive
a call. A step returns a `Step` structure inside Lean; each export projects one field, and the compiler removes the
structure. `make test-lean` fails to link if any Lean runtime symbol is left.

## What is ported

Every engine's sample arithmetic is Lean. The modules, each with an `Api` twin of C entry points and a C loop file
in `voices/`:

| Module | Engines | Glue |
|---|---|---|
| `Firmware/Analog.lean` | saw, variable saw, CSAW, square, triangle, sine, triangle fold, sine fold, buzz (with sync in and out) | `analog_glue.c` |
| `Firmware/Digital.lean` | FM, feedback FM, chaotic FM, triple ring mod, toy, digital modulation | `digital_glue.c` |
| `Firmware/Filters.lean` | saw swarm, the four digital filters, vosim, harmonics | `filters_glue.c` |
| `Firmware/Vowels.lean` | vowel, FOF vowel, question mark | `vowels_glue.c` |
| `Firmware/Wavetables.lean` | wavetables, wave map, wave line, paraphonic waves | `wavetables_glue.c` |
| `Firmware/Noise.lean` | filtered, twin peaks, clocked and particle noise, granular cloud | `noise_glue.c` |
| `Firmware/Percussion.lean` | kick, snare, cymbal, struck bell, struck drum, and Braids' `Svf` and `Excitation` | `percussion_glue.c` |
| `Firmware/Physical.lean` | comb filter, plucked, bowed, blown, fluted | `physical_glue.c` |
| `Firmware/Macro.lean` | the macro oscillator's mixing of the above | `macro_glue.c` |
| `Firmware/Smooth.lean` | the per-sample smoothing of a parameter and of the phase step across a block | `analog_glue.c`, `digital_glue.c`, `macro_glue.c` (included next to the engine's own Api) |
| `Firmware/Pitch.lean` | the pitch to phase step of both Braids oscillators (clamp, fold into the table's octave, blend, shift) | `pitch_glue.c` |

What stays C++ in `voices/braids/`: the per-block setup other than the phase step (filter coefficients, which waves
or partials a block uses, the hysteresis on parameters), the delay lines and state arrays (the glue does every
load and store; Lean gets numbers and returns the numbers to store), and Braids' random number generator (the
glue draws the numbers and passes them in, so the sequence is the one Braids produces).

## How a port is checked

- `make test-lean` (also in `make check`): builds Braids unchanged from `tests/reference/` and the firmware's version
  side by side, with the original's namespace renamed, and compares every output sample.
  - `tests/analog_diff.cc`: the nine oscillators, 6000 blocks each, random pitch and parameter, random sync pulses,
    with and without the sync output. Also prints the time per sample of both.
  - `tests/voice_diff.cc`: the whole voice, all 48 shapes, 58 million samples: random pitch and parameters with
    note strikes, then a long run at a steady pitch (the digital modulation's symbol stream and the question
    mark's whole message take that long). This is the guard for every port.
  - Each port was also checked by mutation: changing one constant in the Lean must make the test report
    differences. The steady runs were added when a mutation went unnoticed.
- `make proofs` lists what is proved about the Lean arithmetic (see `docs/PROOFS.md`): the edge corrections stay in
  range, and the triangle's sample is exactly the sum of its halves, so it cannot wrap.

## What is trusted

- The tables (every `@[extern "fm1_braids_*"]` in `Firmware/`): Braids' data, read by C accessors in
  `voices/braids/analog_oscillator.cc`, `digital_oscillator.cc` and `lean_*_tables.cc`. The Lean code blends neighbouring entries; the differential test shows
  the blend matches the original over the real tables.
- Division by zero: Lean gives 0, C++ would trap. The step is above 65536 for any audible pitch, so the engine never
  divides by zero; the proofs do not cover a step below that.
- Lean's compiler, JieLi's and Lean's clang, and the C glue.

## Traps found while porting

- Lean's `>>>` and `<<<` bind tighter than `*` and `+`, the opposite of C. `t * t >>> 18` is `t * (t >>> 18)`.
  The first port had exactly this bug; the differential test found it at once. Parenthesize every shifted product.
- Braids' interpolation helpers return `int16_t`, so their result is cut to 16 bits before the next step. Leaving it
  in 32 bits matched everywhere except in the buzz at extreme pitches (five samples in a million).
- The product inside `Interpolate824` and `Crossfade` overflows `int32_t` whenever the two values are more
  than 32767 apart, which the comb tables (steps up to 32495, so not quite) and the waves (byte steps up to
  253, so yes) and any crossfade of two far-apart waves can reach. Braids' C++ wraps in practice and so does the
  Lean; `blend_sixteen_between` and `wavetables_read_between_bytes` prove the wrap is exactly cancelled by the
  cut to 16 bits, so the result is the intended value. No code was changed for it.
- A structure that crosses an `if` stays an object and allocates. Write each result as its own `let`.

- `int32_t * uint32_t` in C++ is unsigned: the exciter's decay (`Excitation::Process`) multiplies that way and
  shifts logically. Signed in Lean, the kick and snare differed.
- A filter's high-pass output is not clipped in Braids; typing it `Int16` in the step record cut it.
- Braids' `int8_t` delay lines: the glue sign-extends on load and truncates on store; Lean sees `Int32` in and
  returns the byte.

## What is not done

- The proofs about the engines (`make proofs`, `docs/PROOFS.md`) cover arithmetic facts, not sound: the blep
  corrections' range and the triangle's (`Proofs/Analog.lean`); every table index the Lean code hands to the
  `extern` accessors stays inside its table (`Proofs/Tables.lean`: 257-entry tables at any phase, the 129-entry
  resonator tables thanks to the pitch clamp, the 129-byte waves thanks to the halved phase, the shapers for any
  16-bit index, and the swarm's unmasked sum by its range); a harmonic glides to its target without overshoot;
  an exciter's pulse and a particle burst only decay between hits; one step of the plucked string's loop never
  gains; a wavetable sample is the sum of its halves (`Proofs/Filters.lean`, `Noise.lean`, `Percussion.lean`,
  `Physical.lean`, `Wavetables.lean`); the two blends every table read is built from land between the values
  they blend, so the sine never exceeds its table, a wave crossfade never exceeds its waves and a macro mix is
  never louder than its louder input (`Proofs/Blend.lean`, `Analog.lean`, `Wavetables.lean`, `Digital.lean`);
  the samples of the comb, plucked, bowed and fluted engines, the blown pipe's output filter, the snare,
  cymbal, bell and drum partials, the drum mix, and the noise resonators, boost, burst and grains are the exact
  arithmetic clipped, not wrapped, under the ranges the glue hands over, and the friction, jet, overdrive and
  grain-envelope reads stay inside their tables (`Proofs/Physical.lean`, `Percussion.lean`, `Noise.lean`).
  The bowed string's body filter is the one place the Lean differs from Braids: its state is held within 2^18
  (`Physical.bodyState`, never reached in the test) so that the range its sample proof needs is a proved
  invariant (`physical_bowed_body_stays_bounded`) and not an assumption about numbers Braids never clips.
  The guarantee that the engines sound like Braids is the differential test.
- Samples that Braids itself can overflow are not proved: the kick's low-pass step, the blown pipe's reed
  product and the state-variable filter's cutoff times high-pass can pass 32 bits at the extremes of their
  clipped states, and the clocked noise's quantized value can pass 16 bits; the Lean matches Braids there.
- Indexes that depend on C data are not proved: the comb zone (0 to 14), the formant amplitude (0 to 15), the
  bowing and blowing envelope pointers (clamped per block by C++) and the question mark's position in its code
  table (bounded by the stop symbol in the data). The grain envelope read is proved only given the per-block
  reset and the rate table's top value.
- The chip's CPU cost of the Lean path is unmeasured; on x86 the analog oscillators run at about 1.3 times the
  original's time per sample.
