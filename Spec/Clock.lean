import Firmware.Clock
import Spec.Run

/-- The ticks `clock_poll` in `dinghy.c` feeds the lanes over a run of main-loop passes, `gaps` being the
milliseconds from one pass to the next: each pass the accumulator takes its gap on at `bpm` and the punch
`tempo`, then the loop fires a tick for every tick length `len` the accumulator holds and keeps the rest.
Straight time only: one `len` for the whole run, where swing would change it from tick to tick. -/
def Clock.loop (bpm tempo len acc : UInt32) : List UInt32 → List Lane.Op
  | [] => []
  | dt :: gaps =>
    let acc := Clock.advance acc dt bpm tempo
    List.replicate (Clock.ticksDue acc len).toNat .tick ++
      Clock.loop bpm tempo len (Clock.remainder acc len) gaps

/-- The milliseconds a run of passes covers. -/
def Clock.elapsed (gaps : List UInt32) : Nat := (gaps.map UInt32.toNat).sum
