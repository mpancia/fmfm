set_option compiler.extract_closed false

/-!
# Clock

The sequencer clock runs at 24 ticks a quarter note. `dinghy.c` keeps an accumulator in ten-thousandths of a
straight tick: each pass of the main loop adds what `dt` milliseconds are worth at the tempo (bpm * 4
hundred-thousandths of a tick a millisecond, scaled by the HALF or DOUBLE punch key), then fires a tick and
takes a tick's length (`Swing.tickLength`) off the accumulator for as long as a whole tick is in it.
-/

/-- The accumulator after `dt` milliseconds at `bpm`, with `tempo` the punch-key scale in percent (50 for
HALF, 100, 200 for DOUBLE): `acc + dt * bpm * 4 * tempo / 100`, in the order `dinghy.c` evaluates it. -/
@[inline] def Clock.advance (acc dt bpm tempo : UInt32) : UInt32 :=
  acc + dt * bpm * 4 * tempo / 100

/-- How many ticks of length `len` the accumulator holds: what the firmware's `while (acc >= len)` loop fires. -/
@[inline] def Clock.ticksDue (acc len : UInt32) : UInt32 :=
  acc / len

/-- What the accumulator holds once those ticks are taken off it. -/
@[inline] def Clock.remainder (acc len : UInt32) : UInt32 :=
  acc % len
