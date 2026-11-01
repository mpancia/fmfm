import Firmware.Reverb

/-!
Trips round the tank, built from the loop in `Firmware/Reverb.lean` (which is what `fx/reverb_glue.c` runs),
so a promise about a whole trip can be stated.
-/

/-- A value read from the delay memory, straight or between two neighbours: at most 8.0 in size, since the
memory holds 16 bits of the signal divided by 8. -/
def Reverb.fromMemory (sample : Int32) : Prop := sample.toInt.natAbs ≤ 262144

/-- Half a trip round an undriven tank: a sample read from one long delay, through a loop with no input and
nothing in its allpass lines or its low-pass, to what the other long delay stores. -/
def Reverb.halfTrip (tail decay bright diffusion : Int32) : Int16 :=
  Reverb.compress (Reverb.loop 0 tail 0 0 0 decay bright diffusion)

/-- A full trip round an undriven tank: half through the first loop, then half through the second, which has
the opposite sign of diffusion. -/
def Reverb.roundTrip (tail decay bright diffusion : Int32) : Int16 :=
  Reverb.halfTrip (Reverb.decompress (Reverb.halfTrip tail decay bright diffusion)) decay bright (-diffusion)

/-- A sample after `n` full trips round an undriven tank, read back from the memory after each: trip 0 is the
sample itself. -/
def Reverb.trips (tail decay bright diffusion : Int32) : Nat → Int32
  | 0 => tail
  | n + 1 =>
    Reverb.decompress (Reverb.roundTrip (Reverb.trips tail decay bright diffusion n) decay bright diffusion)
