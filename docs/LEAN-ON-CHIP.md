# Lean code on the FM-1

Code in `Firmware/` is Lean that runs on the chip and in the simulator. Lean's compiler turns it into C,
`tools/build_lean_fw.sh` compiles that C for the target, and it is linked into the firmware next to
`fw/firmware/src/dinghy.c`, which calls it through `rt/fm1_lean.h`.

```
Firmware/*.lean --lake--> C --clang--> objects ┐
rt/lean_rt.c ---------------clang-------------┼--ld--> firmware (chip: pi32v2, simulator: wasm32)
Lean's Init library --lean -c, clang--> libInit.a ┘   (only the parts used are linked)
dinghy.c (hand-written C) ---------------------┘
```

## Two kinds of Lean code

| | Example | May use | Where it may run |
|---|---|---|---|
| Scalar | `Firmware/Kernels.lean` | `UInt8..64`, `Int8..32`, `Bool` | anywhere, including the audio interrupt (no runtime needed) |
| Ordinary | `Firmware/Lane.lean` | structures, `Option`, `Nat` below 2^31, closures | the main loop only (it allocates) |

## What the runtime (`rt/lean_rt.c`) provides
A fixed pool (64 KiB by default, `FM1_LEAN_POOL_BYTES`), size-class free lists, reference-counted freeing, arrays,
panic reporting. It does **not** provide big numbers (any `Nat`/`Int` of 2^31 or more stops the firmware with
"number too big"; a `UInt32` of 2^31 or more converted with `toNat` does this), threads, tasks, IO, or
external objects. If the pool runs out, the firmware stops ("Lean pool exhausted"). On the chip a stop is an
illegal instruction, which Dinghy's crash screen reports; in the simulator the page shows the message.

## Rules for the C side
- Every `@[export]` function takes its arguments **owned**. `lane = fm1_lane_tick(lane)` is right. To read
  without losing `t`, use the `_of` wrappers in `rt/fm1_lean.h` (they `lean_inc` first).
- New export? Add its prototype to `rt/fm1_lean.h`.
- Do not call Lean from interrupts. Keep the audio path scalar.
- Lean's compiler is run with `compiler.extract_closed false` (set in each file, and for `Init`), so no module
  initialisation is needed. Keep that line in every new `Firmware/` file.

## Checks
- `make lean-check`: links the Lean code for the chip with only the runtime and `Init`. Fails on any missing
  symbol, i.e. any Lean feature the runtime lacks.
- `make test`: boots the web build in node, checks the lanes make sound, PLAY stops every note, and the screen moves.
- Proofs: `lake build` (and `make check` for the kernel replay).

## Trusted, not proved
The runtime, Lean's C generator, JieLi's clang, and the C that calls the Lean code. JieLi's clang crashes on two
`Init` modules (`Init.Tactics`, `Init.Data.Order.PackageFactories`); `tools/build_lean_init.sh` skips them and the
link would fail loudly if firmware code needed anything from them.

## Status
- Tested: `make test` runs the web build in node (sound, PLAY, screen) and the chip link builds. The lane code is
  proved in `Proofs/Lane.lean`.
- Not tested: the chip build on a real FM-1. Not measured: time and RAM cost of Lean calls on the chip, or whether
  the 64 KiB pool is enough for four lanes (the simulator reports no pool trouble).
