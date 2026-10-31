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

| Engine | Lean | Notes |
|---|---|---|
| all nine analog oscillators: saw, variable saw, CSAW, square, triangle, sine, triangle fold, sine fold, buzz | yes | including sync in and out |
| digital engines (FM, vowels, strings, drums, wavetables, noise, 30 more) | no | C++ |

The 48 macro shapes are built from these. A shape is only as ported as the oscillators it uses.

## How a port is checked

- `make test-lean` (also in `make check`): builds Braids unchanged from `tests/reference/` and the firmware's version
  side by side, with the original's namespace renamed, and compares every output sample.
  - `tests/analog_diff.cc`: the nine oscillators, 6000 blocks each, random pitch and parameter, random sync pulses,
    with and without the sync output. Also prints the time per sample of both.
  - `tests/voice_diff.cc`: the whole voice, all 48 shapes, 1.15 million samples. This is the guard for every
    port: a shape that is still C++ must stay identical, and a ported one must too.
- `make proofs` lists what is proved about the Lean arithmetic (see `docs/PROOFS.md`): the edge corrections stay in
  range, and the triangle's sample is exactly the sum of its halves, so it cannot wrap.

## What is trusted

- The tables (`Analog.sineTable`, `sineFoldTable`, `triFoldTable`, `combTable`, each an `extern`): Braids' data, read
  by C accessors in `analog_oscillator.cc`. The Lean code blends neighbouring entries; the differential test shows
  the blend matches the original over the real tables.
- Division by zero: Lean gives 0, C++ would trap. The step is above 65536 for any audible pitch, so the engine never
  divides by zero; the proofs do not cover a step below that.
- Lean's compiler, JieLi's and Lean's clang, and the C glue.

## Traps found while porting

- Lean's `>>>` and `<<<` bind tighter than `*` and `+`, the opposite of C. `t * t >>> 18` is `t * (t >>> 18)`.
  The first port had exactly this bug; the differential test found it at once. Parenthesize every shifted product.
- Braids' interpolation helpers return `int16_t`, so their result is cut to 16 bits before the next step. Leaving it
  in 32 bits matched everywhere except in the buzz at extreme pitches (five samples in a million).
- A structure that crosses an `if` stays an object and allocates. Write each result as its own `let`.

## Order of the rest

1. Digital engines with scalar state: FM, feedback FM, chaotic FM, digital modulation, toy, triple ring mod.
2. Engines with tables and filters: vosim, vowels, digital filters, saw swarm, harmonics.
3. Engines with delay lines and big state (comb, plucked, bowed, blown, fluted, bells, drums, granular): these need
   arrays, so they need either a runtime that is safe in the interrupt or state kept in C memory.
