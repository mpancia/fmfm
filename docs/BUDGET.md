# The audio budget

What a sample costs, and whether it fits the FM-1's audio interrupt. Nothing here was measured on an FM-1; this
is an estimate from the host build and the chip's disassembly, with its assumptions listed.

## What the chip gives

- AC7911B: a pi32v2 core, "DC to 320 MHz" in the datasheet. The stock bootloader sets the clock and Dinghy keeps
  it; the value is not known to us. The numbers below are given at 160, 240 and 320 MHz.
- 44.1 kHz, so one sample has 3628 cycles at 160 MHz, 5442 at 240 MHz, 7256 at 320 MHz.
- `app_audio` gets 256 frames at a time, 5.8 ms. The USB and key-scan interrupts take some of it; Dinghy's rule
  (`fw/docs/RULES.md`) is to stay under half.
- The core has a 32x32 to 64-bit multiply-accumulate (`r1_r0 += r4 * r2`) and a 64-bit shift, so a Q15 multiply
  is two instructions. It has a hardware divide of unknown cost.

## How it was measured

`tools/perf_host.sh` builds the firmware for this computer (Dinghy's host mode, `fw/tests/host.c`) with the Lean
code and the Braids voice linked in, compiled by Lean's clang as 32-bit x86, and counts the instructions the
renders take per sample with a Linux perf counter. Scripts hold keys, stop the lanes and turn knobs.

Two checks on the method:

- gcc's `-Os` left `lean_int64_of_nat` calls in the Lean code (every `Int64` literal became a runtime unboxing);
  JieLi's clang folds them (the chip's `write_line` is `r0 = 16384; r1_r0 += r4 * r2; r1_r0 >>= 15`). The host
  build therefore uses clang; with gcc the same code counted 4 to 7 times more.
- The reverb's chip disassembly (`fm1_reverb_block` and its helpers, pi32v2) is 152 instructions in the loop plus
  2 x 39 (`read_modulated`), 8 x 22 (`read_line`) and 12 x 26 (`write_line`): about 720 a sample. The host count for
  the same thing is 628. So a host instruction is about 1.15 chip instructions here.

## What it costs

Host instructions a sample (clang, 32-bit x86); multiply by about 1.15 for chip instructions.

| Case | A sample |
|---|---|
| Nothing sounding, reverb and delay off | 12 |
| The delay alone (both lines running, nothing sounding) | 163 |
| INIT patch, four lanes, reverb off | 464 |
| Reverb alone (lanes stopped, tail running) | 628 |
| INIT patch with its reverb (the default) | 1086 |
| Six voices of CSAW held, reverb off | 1881 |
| Six voices of CSAW held, reverb on | 2498 |
| Six voices of 3 SQR (the costliest shape), reverb off | 3230 |
| Six voices of 3 SQR, reverb on | 3835 |

The six-voice rows are averaged over a run that is a quarter silent, so the sounding part is about a third more:
3 SQR is about 700 a voice; CSAW about 400. Of 48 shapes, 3 SQR, WAVE LINE, WAVE PARA, WAVE MAP and HARMONIC are the
costly ones (2900 to 3230 for six); most sit at 2400 to 2600.

## Does it fit

Assume one chip instruction a cycle plus a third for memory and the divides (1.3 cycles an instruction), and the
1.15 ratio:

| Case | Chip cycles a sample | At 160 MHz | At 240 MHz | At 320 MHz |
|---|---|---|---|---|
| INIT with reverb | 1600 | 45% | 30% | 22% |
| Six CSAW with reverb | 3700 | 100% | 68% | 51% |
| Six 3 SQR with reverb (worst) | 6600 | 180% | 120% | 90% |

So: the default patch fits at any plausible clock, inside Dinghy's half-budget rule at 240 MHz and above. Full
polyphony of a cheap shape with reverb fits at 240 MHz. Six voices of the costliest shapes with reverb do not fit
at 240 MHz and are marginal at 320 MHz. The lanes play four sounds through six voices, so the worst case needs
long releases of a costly shape on every lane.

If it crackles on a real FM-1, in order of least damage:

1. `fm1_ticks()` around `app_audio` to replace this estimate with a measurement (Dinghy's `RULES.md` shows how).
2. `NV` from 6 to 4 in `dinghy.c`: one voice a lane, no overlap of releases.
3. The reverb's `compress` divides by 8 with the hardware divider (round toward zero, as Clouds' float cast does);
   twelve divides a sample. An arithmetic shift rounds toward minus infinity, one LSB off for negative samples, and
   would need `reverb_compress_saturates` restated.
4. Skip the reverb when more than four voices sound.

## What is not known

- The clock. The datasheet's ceiling is 320 MHz; 160 or 240 MHz would be ordinary choices.
- Cycles an instruction on pi32v2, the divide's cost, cache behaviour on a 64 KiB ring read at ten places.
- Whether Dinghy's own yardstick (sloopDX's engines at "about 1000 to 1500" on the host) was measured with gcc or
  clang; against it the default patch is at the low end and six costly voices are three times over.
