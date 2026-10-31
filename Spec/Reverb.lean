import Firmware.Reverb

/-!
The tank's loops as `fx/reverb_glue.c` runs them for one sample, with the samples read from the delay memory
as parameters. The C owns the memory and the filter states; these definitions only record the order of the
arithmetic, so a promise about a whole trip round the tank can be stated.
-/

/-- A value read from the delay memory, straight or between two neighbours: at most 8.0 in size, since the
memory holds 16 bits of the signal divided by 8. -/
def Reverb.fromMemory (sample : Int32) : Prop := sample.toInt.natAbs ≤ 262144

/-- One allpass on the accumulator: add the line's oldest sample times the opposite gain, store that sum, and
pass on the sum times the gain plus the oldest sample. -/
def Reverb.allpass (acc oldest gain : Int32) : Int32 :=
  let summed := acc + Reverb.mul oldest (-gain)
  Reverb.mul summed gain + oldest

/-- The four input diffusers: the send times the input gain, through four allpasses with the negative of the
diffusion as their gain. `oldest1` to `oldest4` are the samples read from their lines. -/
def Reverb.diffuse (send inputGain diffusion oldest1 oldest2 oldest3 oldest4 : Int32) : Int32 :=
  let fed := Reverb.mul send inputGain
  let afterFirst := Reverb.allpass fed oldest1 (-diffusion)
  let afterSecond := Reverb.allpass afterFirst oldest2 (-diffusion)
  let afterThird := Reverb.allpass afterSecond oldest3 (-diffusion)
  Reverb.allpass afterThird oldest4 (-diffusion)

/-- A loop's low-pass output: the diffused input plus the sample read from the other loop's long delay times
the decay gain, smoothed from `state`. This is also the low-pass's state for the next sample. -/
def Reverb.loopSmooth (input tail state decay bright : Int32) : Int32 :=
  Reverb.lowpass state (input + Reverb.mul tail decay) bright

/-- One loop of the tank, from the diffused input to the sum it stores in its long delay: the low-pass
output through the loop's two allpasses, with `diffusion` then its negative as their gains. The first loop
has the glue's `k_diffusion` as `diffusion`, the second its negative. -/
def Reverb.loop (input tail state oldestA oldestB decay bright diffusion : Int32) : Int32 :=
  let afterA := Reverb.allpass (Reverb.loopSmooth input tail state decay bright) oldestA diffusion
  Reverb.allpass afterA oldestB (-diffusion)

/-- Half a trip round an undriven tank: a sample read from one long delay, through a loop with no input and
nothing in its allpass lines or its low-pass, to what the other long delay stores. -/
def Reverb.halfTrip (tail decay bright diffusion : Int32) : Int16 :=
  Reverb.compress (Reverb.loop 0 tail 0 0 0 decay bright diffusion)

/-- A full trip round an undriven tank: half through the first loop, then half through the second, which has
the opposite sign of diffusion. -/
def Reverb.roundTrip (tail decay bright diffusion : Int32) : Int16 :=
  Reverb.halfTrip (Reverb.decompress (Reverb.halfTrip tail decay bright diffusion)) decay bright (-diffusion)
