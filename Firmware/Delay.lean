import Firmware.Reverb

set_option compiler.extract_closed false

/-!
# Delay send: the arithmetic

A tempo-synced delay on the same send bus as the reverb: one delay line, read a note value behind the write
position, fed back through a low-pass. This file holds the arithmetic of one sample as scalar functions;
`fx/delay_glue.c` owns the line and runs it. Signals are Q15 in `Int32` as in `Firmware/Reverb.lean`, whose
`mul` and `lowpass` are used; the line stores whole 16-bit samples (no headroom above 1.0 is needed because
the feedback is below 1.0 and the input is saturated on the way in).
-/

/-- Samples in the delay line (a power of two): 743 ms at 44.1 kHz. -/
@[inline] def Delay.ring : UInt32 := 32768

/-- Position in the line of the sample `offset` places before the write position. -/
@[inline] def Delay.pos (write offset : UInt32) : UInt32 := (write + offset) &&& 32767

/-- The write position one sample later: backwards through the line, like the reverb's. -/
@[inline] def Delay.nextWrite (write : UInt32) : UInt32 := (write + 32767) &&& 32767

/-- The note values a TIME setting can pick, as a fraction of a quarter note: 1/32, 1/16, 1/8 triplet,
dotted 1/16, 1/8, 1/4 triplet, dotted 1/8, 1/4. This is the numerator (a pair would be a boxed constant that
needs module initialisation, which the chip has none of). -/
@[inline] def Delay.numerator (time : UInt32) : UInt32 :=
  match time with
  | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 3 | 4 => 1 | 5 => 2 | 6 => 3 | _ => 1

/-- The denominator of the same fraction. -/
@[inline] def Delay.denominator (time : UInt32) : UInt32 :=
  match time with
  | 0 => 8 | 1 => 4 | 2 => 3 | 3 => 8 | 4 => 2 | 5 => 3 | 6 => 4 | _ => 1

/-- Samples for a TIME setting at `bpm` and `rate` Hz: a quarter note is `60 * rate / bpm` samples. Held to
the line: at least 1 and at most 32767 (so slow tempos with long notes get the longest delay there is).
`bpm` 0 counts as 40. -/
@[inline] def Delay.samples (time bpm rate : UInt32) : UInt32 :=
  let tempo := if bpm = 0 then 40 else bpm
  let n := 60 * rate * Delay.numerator time / (tempo * Delay.denominator time)
  if n > 32767 then 32767 else if n = 0 then 1 else n

/-- Feedback gain for a setting of 0 to 100: 0 to 0.95 in Q15. Below 1, so echoes always die away. -/
@[inline] def Delay.feedbackGain (feedback : UInt32) : Int32 := (31129 * min feedback 100 / 100).toInt32

/-- Low-pass amount in the feedback for a tone setting of 0 to 100: 0.2 to 1.0 in Q15 (1.0 is no filtering). -/
@[inline] def Delay.toneGain (tone : UInt32) : Int32 := (6554 + 26214 * min tone 100 / 100).toInt32

/-- A signal for the line: held to the 16-bit range instead of wrapping. -/
@[inline] def Delay.store (signal : Int32) : Int16 :=
  if signal > 32767 then 32767 else if signal < -32768 then -32768 else signal.toInt16

/-- A stored sample back to Q15. -/
@[inline] def Delay.fetch (stored : Int16) : Int32 := stored.toInt32

/-- What goes into the line: the send plus the filtered echo times the feedback gain. -/
@[inline] def Delay.input (send filtered feedback : Int32) : Int32 := send + Reverb.mul filtered feedback
