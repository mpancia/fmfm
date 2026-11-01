import Firmware.Swing

set_option compiler.extract_closed false

/-- C entry: the length of tick `phase` of the quarter note at `swing`, in ten-thousandths of a tick. -/
@[export fm1_swing_tick_length] def swingTickLength (phase swing : UInt32) : UInt32 :=
  Swing.tickLength phase swing
