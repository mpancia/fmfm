set_option compiler.extract_closed false

/-!
# Swing

The clock runs at 24 ticks a quarter note, so an eighth note is 12 ticks. Swing lengthens the first eighth of
each pair and shortens the second by the same amount, so a pair of eighths still takes exactly its time and
the bar never drifts. `dinghy.c` counts tick time in units of a ten-thousandth of a tick and asks here how long
tick `n` of the 24 in a quarter note is.
-/

/-- The length of one tick, in ten-thousandths of a straight tick, for a `swing` setting of 0 to 100: at 0 every
tick is 10000; at 100 the ticks of the first eighth are 16666 and those of the second 3334 (a 2:1 triplet feel is
swing 67). `phase` is the tick's place in the quarter note (0 to 23, taken modulo 24). -/
@[inline] def Swing.tickLength (phase swing : UInt32) : UInt32 :=
  let s := min swing 100
  let first := 10000 + 6666 * s / 100
  if phase % 24 < 12 then first else 20000 - first
