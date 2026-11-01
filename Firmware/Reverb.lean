set_option compiler.extract_closed false

/-!
# Reverb send: the arithmetic

The reverb is Clouds' (Mutable Instruments, MIT): four allpass diffusers feeding two cross-coupled loops of
two allpasses and a long delay, with two slow LFOs smearing some of the delay times. This file holds the
arithmetic of one sample as scalar functions; `fx/reverb_glue.c` owns the delay memory and runs the network
in Clouds' order.

Numbers: signals are Q15 (32768 is 1.0) in `Int32`; gains are Q15; the delay memory stores each sample
as 16 bits holding the signal times 4096, as Clouds' 12-bit format does, so the signal can swing up to 8.0
inside the loops. All delay times scale with `scale` (Q8, 256 is Clouds' 32 kHz sizes; 353 is the same room
at 44.1 kHz).
-/

/-- Samples in the shared delay memory (a power of two). -/
@[inline] def Reverb.ring : UInt32 := 32768

/-- The ten delay lines at Clouds' 32 kHz, in samples: four input allpasses, then each loop's two allpasses
and long delay. -/
@[inline] def Reverb.baseLength (line : UInt32) : UInt32 :=
  match line with
  | 0 => 113 | 1 => 162 | 2 => 241 | 3 => 399 | 4 => 1653
  | 5 => 2038 | 6 => 3411 | 7 => 1913 | 8 => 1663 | _ => 4782

/-- A delay line's length at the chosen scale. -/
@[inline] def Reverb.length (scale line : UInt32) : UInt32 := (Reverb.baseLength line * scale + 128) >>> 8

/-- Where a delay line starts in the shared memory. Lines follow each other with one sample between. -/
@[inline] def Reverb.start (scale line : UInt32) : UInt32 :=
  let len := Reverb.length scale
  match line with
  | 0 => 0
  | 1 => len 0 + 1
  | 2 => len 0 + len 1 + 2
  | 3 => len 0 + len 1 + len 2 + 3
  | 4 => len 0 + len 1 + len 2 + len 3 + 4
  | 5 => len 0 + len 1 + len 2 + len 3 + len 4 + 5
  | 6 => len 0 + len 1 + len 2 + len 3 + len 4 + len 5 + 6
  | 7 => len 0 + len 1 + len 2 + len 3 + len 4 + len 5 + len 6 + 7
  | 8 => len 0 + len 1 + len 2 + len 3 + len 4 + len 5 + len 6 + len 7 + 8
  | 9 => len 0 + len 1 + len 2 + len 3 + len 4 + len 5 + len 6 + len 7 + len 8 + 9
  | _ => len 0 + len 1 + len 2 + len 3 + len 4 + len 5 + len 6 + len 7 + len 8 + 9

/-- Position in the ring of the sample `offset` places from the newest one in a line that starts at `base`.
`write` is the current write position. -/
@[inline] def Reverb.pos (write base offset : UInt32) : UInt32 := (write + base + offset) &&& 32767

/-- The write position one sample later: it moves backwards through the ring. -/
@[inline] def Reverb.nextWrite (write : UInt32) : UInt32 := (write + 32767) &&& 32767

/-- A signal for the delay memory: the signal times 4096 (as Q15 divided by 8), cut to 16 bits. A signal
beyond 8.0 saturates instead of wrapping. -/
@[inline] def Reverb.compress (signal : Int32) : Int16 :=
  let stored := signal / 8
  if stored > 32767 then 32767 else if stored < -32768 then -32768 else stored.toInt16

/-- A stored sample back to Q15. -/
@[inline] def Reverb.decompress (stored : Int16) : Int32 := stored.toInt32 * 8

/-- A signal times a Q15 gain, rounded. -/
@[inline] def Reverb.mul (signal gain : Int32) : Int32 :=
  ((signal.toInt64 * gain.toInt64 + 16384) >>> 15).toInt32

/-- One step of a low-pass filter: the state moves from `state` towards `signal` by the Q15 amount
`coefficient`. -/
@[inline] def Reverb.lowpass (state signal coefficient : Int32) : Int32 :=
  state + Reverb.mul (signal - state) coefficient

/-- A point between two stored neighbours, `fraction` of the way from `a` to `b` (Q16, below 65536). -/
@[inline] def Reverb.interpolate (a b fraction : Int32) : Int32 :=
  a + (((b - a).toInt64 * fraction.toInt64) >>> 16).toInt32

/-- A sine of a 32-bit phase, from -32767 to 32767: a parabola, corrected towards a sine (error about
0.1%). -/
@[inline] def Reverb.sine (phase : UInt32) : Int32 :=
  let x : Int32 := phase.toInt32 >>> 16
  let ax := if x < 0 then 0 - x else x
  let y := (x * (32768 - ax)) >>> 13
  let ay := if y < 0 then 0 - y else y
  let y := y + (((((y * ay) >>> 15) - y) * 7373) >>> 15)
  if y > 32767 then 32767 else if y < -32767 then -32767 else y

/-- The slow wobble: half plus half a cosine of the phase, from 0 to 32767 (Q15), as Clouds' LFOs do. -/
@[inline] def Reverb.lfo (phase : UInt32) : Int32 := (Reverb.sine (phase + 1073741824) + 32768) >>> 1

/-- A delay time that moves with an LFO, in samples as Q16: `base` samples, plus up to `depth` samples, both
at Clouds' sizes and scaled. `lfo` is the wobble from `Reverb.lfo`. -/
@[inline] def Reverb.modOffset (base depth scale lfo : UInt32) : UInt32 :=
  ((base * scale) <<< 8) + ((depth * scale * lfo) >>> 7)

/-- Loop gain for a decay-time setting of 0 to 100 (more is the same as 100): 0.35 to 0.98 in Q15. Below 1,
so the tail always dies away. -/
@[inline] def Reverb.timeGain (time : UInt32) : Int32 := (11469 + (20644 * (min time 100)) / 100).toInt32

/-- Low-pass amount for a brightness setting of 0 to 100: 0.6 to 0.97 in Q15. Higher is brighter. -/
@[inline] def Reverb.brightGain (bright : UInt32) : Int32 :=
  (19661 + (12124 * (min bright 100)) / 100).toInt32

/-! The tank, as `fx/reverb_glue.c` runs it for one sample, with the samples it reads from the delay memory as
parameters. The glue owns the memory and the filter states and calls `allpassStore`, `allpassOut`, `lowpass`
and `mul` in this order; these definitions are that order written down, and what `Spec/Reverb.lean` builds
its trips from. -/

/-- One allpass, the half that goes into its line: the accumulator plus the line's oldest sample times the
opposite gain. The glue stores this. -/
@[inline] def Reverb.allpassStore (acc oldest gain : Int32) : Int32 := acc + Reverb.mul oldest (-gain)

/-- The other half, what the allpass passes on: the stored sum times the gain plus the oldest sample. -/
@[inline] def Reverb.allpassOut (summed oldest gain : Int32) : Int32 := Reverb.mul summed gain + oldest

/-- One allpass on the accumulator, both halves. -/
def Reverb.allpass (acc oldest gain : Int32) : Int32 :=
  Reverb.allpassOut (Reverb.allpassStore acc oldest gain) oldest gain

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

