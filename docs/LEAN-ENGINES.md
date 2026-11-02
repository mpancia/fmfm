# Braids engines in Lean

The sound engines are Mutable Instruments' Braids, ported from C++ to Lean. The firmware runs the Lean, which is
checked against the original two ways: it must produce the same samples, and the arithmetic has proofs.

## How a port is built

```
Firmware/Analog.lean       the arithmetic of one sample: pure scalar functions (UInt32, Int32, Int16)
Firmware/AnalogApi.lean    one export per result field, so every call returns a plain number
        |  lake: Lean -> C
voices/analog_glue.c       includes that C as inline functions; owns the buffers and the sample loop
voices/braids/analog_oscillator.cc   the C++ class calls the glue; the control flow listed below is still C++
```

Lean cannot allocate in the audio interrupt, so engine code is scalar only: no `Array`, no structures that survive
a call. A step returns a `Step` structure inside Lean; each export projects one field, and the compiler removes the
structure. `make test-lean` fails to link if any Lean runtime symbol is left.

## What is ported

Every engine's sample arithmetic is Lean. Each module has an `Api` twin of C entry points and a C loop file in
`voices/`:

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
| `Firmware/DigitalSetup.lean` | the per-block setup of the FM, ring modulator, toy and digital modulation engines (FM ratio quantizer, modulator and symbol steps, feedback attenuation, toy decimation) and `ComputeDelay` (the delay-line length of a pitch) | `digital_setup_glue.c` |
| `Firmware/AnalogSetup.lean` | the analog oscillator's per-block setup: the pitch clamp, the square's and variable saw's pulse widths, the buzz's comb zones and crossfade | `analog_setup_glue.c` |
| `Firmware/MacroSetup.lean` | the macro oscillator's per-block setup: CSAW's shift, morph's zone, balance, pulse width, low-pass cutoff and fuzz, the triple detunes (interval table), the sub, sync and buzz pitches, the sine and triangle fold amounts | `macro_setup_glue.c` |
| `Firmware/VoiceSetup.lean` | the voice's doorway (`voices/voice.cc`): the shape guard and the cut of pitch and timbre to Braids' 16 bits | `voice_setup_glue.c` |
| `Firmware/FiltersSetup.lean` | the per-block setup of the saw swarm (detune, the seven steps, the high-pass cutoff), the digital filters (the resonance's target step and its glide per sample), vosim (formant steps) and harmonics (peaks, width, the twelve target amplitudes) | `filters_setup_glue.c` |
| `Firmware/VowelsSetup.lean` | the per-block setup of the vowel (vowel and consonant formant steps, amplitudes and noise, from the phoneme data read through accessors), the FOF vowel (`InterpolateFormantParameter`, the five cutoffs and the amplitude) and the question mark (dit length, noise threshold) | `vowels_setup_glue.c` |
| `Firmware/NoiseSetup.lean` | the per-block setup of the noise engines: the hysteresis on parameters, the filtered noise's cutoff, damping, three gains and gain correction, the twin peaks' coefficients, scales, sharpness and makeup, the clocked noise's shifted step, generator period and quantizer step, the cloud's grain restarts (rate, envelope reset, detuned step; the glue draws the random numbers), the particle density | `noise_setup_glue.c` |
| `Firmware/WavetablesSetup.lean` | the per-block setup of the wavetable engines: which wavetable, steps and waves a block plays and their crossfade, the wave map's corners and crossfades, the wave line's smoothing, scan, waves, mode and balance, the paraphonic chord detunes, voice steps and waves (the wave, line, chord and map tables read through accessors) | `wavetables_setup_glue.c` |
| `Firmware/PercussionSetup.lean` | the per-block setup of the percussion engines: the bell and drum partial tables (offsets, amplitudes, decays) and each partial's pitch, step and decayed amplitude, the drum's cutoff, filter coefficient and gains, the kick's resonance and low-pass, the snare's decay, resonances, levels, frequencies and gains, the hat's seven steps | `percussion_setup_glue.c` |
| `Firmware/PhysicalSetup.lean` | the per-block setup of the physical models: the comb's smoothed pitch and clamped delay, a new string's oversampling, size, mask and fill, the loss and update chance, the bowed, blown and fluted delays with their octave transpositions (a fixed chain of halvings), bow and breath, the body filter (its note held to the table, where Braids reads past it above note 127), the envelope pointer clamps | `physical_setup_glue.c` |

What stays C++ or C in `voices/`:

- the per-block control flow: which `Render` runs, `strike_`/`init_` flags, state resets;
- the delay lines and state arrays. The glue does every load and store; Lean computes every position and every
  value, and `Proofs/Physical.lean` shows each position inside its line;
- the tables (`resources.cc`), read through `fm1_braids_*` accessors;
- Braids' random number generator. The glue draws the numbers and passes them in, so the sequence is the one
  Braids produces.

The per-block setup (pitch to phase step, filter coefficients, which waves or partials a block uses, the
hysteresis on parameters) is Lean in the `*Setup.lean` modules, so the ranges the sample theorems take are
themselves theorems (`Proofs/*Setup.lean`). The facts about table data they rest on are theorems about the
generated copies in `Firmware/BraidsData.lean` (`Proofs/BraidsData.lean`).

## How a port is checked

- `make test-lean` (also in `make check`) builds Braids unchanged from `tests/reference/` and the firmware's version
  side by side, with the original's namespace renamed, and compares every output sample.
  - `tests/analog_diff.cc`: the nine oscillators, 6000 blocks each, random pitch and parameter, random sync pulses,
    with and without the sync output. Also prints the time per sample of both.
  - `tests/voice_diff.cc`: the whole voice, all 48 shapes, 58 million samples: random pitch and parameters with
    note strikes, then a long run at a steady pitch (the digital modulation's symbol stream and the question
    mark's whole message take that long). This is the guard for every port.
  - Each port is also checked by mutation: changing one constant in the Lean must make the test report
    differences. The steady runs exist because the random run once missed a mutation.
- `make proofs` lists what is proved about the Lean arithmetic (see `docs/PROOFS.md`): the edge corrections stay in
  range, and the triangle's sample is exactly the sum of its halves, so it cannot wrap.

## What is trusted

- The tables (every `@[extern "fm1_braids_*"]` in `Firmware/`): Braids' data, read by one-line C accessors in
  `voices/braids/analog_oscillator.cc`, `digital_oscillator.cc`, `macro_oscillator.cc` and `lean_*_tables.cc`.
  The Lean code blends neighbouring entries; the differential test shows the blend matches the original over
  the real tables. Five tables whose shape the proofs need (the phase steps, the filter cutoff, the grain
  envelope rate, the vowel amplitudes, the wavetable step counts) also have a copy in Lean,
  `Firmware/BraidsData.lean`, generated from the C sources by `tools/gen_tables.py` and kept in step by `make
  lint`. Their accessors' bodies are those copies, and `Proofs/BraidsData.lean` checks the facts (rising, top
  entry, nibbles, at most 16 steps) against them. What is trusted there is only that the C accessor reads the
  same table.
- Division by zero: Lean gives 0, C++ would trap. The step is above 65536 for any audible pitch, so the engine never
  divides by zero; the proofs do not cover a step below that.
- Lean's compiler, JieLi's and Lean's clang, and the C glue.

## Traps

- Lean's `>>>` and `<<<` bind tighter than `*` and `+`, the opposite of C. `t * t >>> 18` is `t * (t >>> 18)`.
  Parenthesize every shifted product. The differential test catches this at once.
- Braids' interpolation helpers return `int16_t`, so their result is cut to 16 bits before the next step. Left
  in 32 bits it matches everywhere except in the buzz at extreme pitches (five samples in a million).
- The product inside `Interpolate824` and `Crossfade` overflows `int32_t` whenever the two values are more
  than 32767 apart. The comb tables (steps up to 32495) stay under; the waves (byte steps up to 253) and any
  crossfade of two far-apart waves do not. Braids' C++ wraps in practice and so does the Lean;
  `blend_sixteen_between` and `wavetables_read_between_bytes` prove the wrap is exactly cancelled by the cut to
  16 bits, so the result is the intended value.
- A structure that crosses an `if` stays an object and allocates. Write each result as its own `let`.
- `int32_t * uint32_t` in C++ is unsigned: the exciter's decay (`Excitation::Process`) multiplies that way and
  shifts logically. Done signed in Lean, the kick and snare differ.
- A filter's high-pass output is not clipped in Braids; typing it `Int16` in the step record cuts it.
- Braids' `int8_t` delay lines: the glue sign-extends on load and truncates on store; Lean sees `Int32` in and
  returns the byte.

## What is not done

- The proofs about the engines (`make proofs`, `docs/PROOFS.md`) cover arithmetic facts, not sound. The guarantee
  that the engines sound like Braids is the differential test. What is proved:
  - the blep corrections' range and the triangle's (`Proofs/Analog.lean`);
  - every table index the Lean code hands to the `extern` accessors stays inside its table (`Proofs/Tables.lean`:
    257-entry tables at any phase, the 129-entry resonator tables by the pitch clamp, the 129-byte waves by the
    halved phase, the shapers for any 16-bit index, and the swarm's unmasked sum by its range);
  - a harmonic glides to its target without overshoot; an exciter's pulse and a particle burst only decay between
    hits; one step of the plucked string's loop never gains; a wavetable sample is the sum of its halves
    (`Proofs/Filters.lean`, `Noise.lean`, `Percussion.lean`, `Physical.lean`, `Wavetables.lean`);
  - the two blends every table read is built from land between the values they blend, so the sine never exceeds
    its table, a wave crossfade never exceeds its waves and a macro mix is never louder than its louder input
    (`Proofs/Blend.lean`, `Analog.lean`, `Wavetables.lean`, `Digital.lean`);
  - the samples of the comb, plucked, bowed and fluted engines, the blown pipe's output filter, the snare,
    cymbal, bell and drum partials, the drum mix, and the noise resonators, boost, burst and grains are the exact
    arithmetic clipped, not wrapped, under the ranges the glue hands over; the friction, jet, overdrive and
    grain-envelope reads stay inside their tables (`Proofs/Physical.lean`, `Percussion.lean`, `Noise.lean`).

  The Lean differs from Braids in two places. The bowed string's body filter state is held within 2^18
  (`Physical.bodyState`, never reached in the test), so the range its sample proof needs is a proved invariant
  (`physical_bowed_body_stays_bounded`) rather than an assumption about numbers Braids never clips. The flute's
  body filter note is held at 127 (`PhysicalSetup.flutedNote`, above the test's pitches), where Braids reads past
  its 128-entry table.
- Samples that Braids itself can overflow are not proved: the kick's low-pass step, the blown pipe's reed
  product and the state-variable filter's cutoff times high-pass can pass 32 bits at the extremes of their
  clipped states, and the clocked noise's quantized value can pass 16 bits. The Lean matches Braids there.
- Indexes that depend on C data are not proved: the question mark's position in its code table (bounded by the
  stop symbol in the data); the wave line's wave after the scan, which reads one past Braids' 64-entry line at the
  top of the parameter's range (Braids' own overrun, kept so the output matches); the wave numbers the selection
  tables hold (`wavetables_setup_wave_in_bank` takes a number up to 255). Proved from setup or table data: the
  bowing and blowing envelope reads, from the clamp after each block (`physical_setup_envelope_pointer_in_table`);
  a new plucked string's size, mask and fill (`physical_setup_pluck_size_valid`); the drum's cutoff read and the
  gains and decays the percussion mixes assume (`Proofs/PercussionSetup.lean`); the grain envelope read, from the
  block's setup and the rate table's top value (`noise_setup_grain_reset`, `braids_data_rate_top`); the vowel's
  formant amplitude (0 to 15) and the swarm's cutoff coefficient's range, from the phoneme data's nibbles and the
  cutoff table's top entry (`Proofs/VowelsSetup.lean`, `Proofs/FiltersSetup.lean`, both checked in
  `Proofs/BraidsData.lean`).
- The chip's CPU cost of the Lean path is unmeasured; on x86 the analog oscillators run at about 1.3 times the
  original's time per sample.
