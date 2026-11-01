import Firmware.Clock

set_option compiler.extract_closed false

/-- C entry: the clock accumulator after `dt` milliseconds at `bpm` and the punch tempo in percent. -/
@[export fm1_clock_advance] def clockAdvance (acc dt bpm tempo : UInt32) : UInt32 :=
  Clock.advance acc dt bpm tempo

/-- C entry: the ticks of length `len` the accumulator holds. -/
@[export fm1_clock_ticks_due] def clockTicksDue (acc len : UInt32) : UInt32 :=
  Clock.ticksDue acc len

/-- C entry: the accumulator once its whole ticks of length `len` are taken off. -/
@[export fm1_clock_remainder] def clockRemainder (acc len : UInt32) : UInt32 :=
  Clock.remainder acc len
