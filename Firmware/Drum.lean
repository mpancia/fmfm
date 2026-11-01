import Firmware.Fm

set_option compiler.extract_closed false

/-!
An 808-style drum voice, synthesised: ten shapes from the same few parts. A sine (`Fm.sineAt`) whose
increment sweeps down to the tuning (the kick and the toms), a 16-bit shift-register noise, one-pole filters
(a low-pass; the high-pass is what the low-pass leaves; a band-pass is the one after the other), six square
oscillators at the 808's hi-hat frequencies, and exponential envelopes a sample at a time.
`voices/drum_glue.c` keeps the state and composes these per shape; the arithmetic of every sample is here.

Fixed point: phases and increments in 32 bits (one cycle is 2^32), samples in Q15 (32767 is one) and the
filters' signals up to twice that, envelopes in Q24 (16777216 is one), filter coefficients in Q14 (16384 is
one), levels in Q13 (8192 is one, so a shape can lift a filtered signal four times), rates as shares of 2^20
a sample, increments of fixed oscillators as `f / 44100 * 2^32`.
-/

/-- One step of the noise: a 16-bit Galois shift register with taps 0xB400 (x^16 + x^14 + x^13 + x^11 + 1,
a primitive polynomial): the state shifts right and, when the bit that fell off was set, the taps flip. From
any nonzero 16-bit state the run visits every other nonzero state before it repeats (`drum_noise_period`). -/
@[inline] def Drum.lfsr (s : UInt32) : UInt32 :=
  if s &&& 1 = 1 then (s >>> 1) ^^^ 0xB400 else s >>> 1

/-- The noise sample from the state, Q15: the state's top 15 bits centred, an odd number from -32767 to
32767. -/
@[inline] def Drum.noise (s : UInt32) : Int32 := (s &&& 0xFFFE).toInt32 - 32767

/-- An envelope one sample on: a share `rate / 2^20` of what is left goes, rounded up so a decaying envelope
always moves and reaches silence rather than stalling on a last few counts (the time constant is `2^20 /
rate` samples: rate 219 is about half a second at 44.1 kHz to a hundredth, 2200 fifty milliseconds). Rate 0
holds. -/
@[inline] def Drum.envelope (env rate : UInt32) : UInt32 :=
  env - (((env >>> 8) * rate + 4095) >>> 12)

/-- A swept increment one sample on: the distance to the target shrinks by a share `rate / 2^20`, and an
increment at or below the target sits on it. -/
@[inline] def Drum.sweep (inc target rate : UInt32) : UInt32 :=
  if inc ≤ target then target else inc - ((((inc - target) >>> 12) * rate) >>> 8)

/-- Where a sweep starts for a tuning and a colour: the tuning (held to 2^27, a 1.4 kHz top) plus up to four
times itself at full colour, so the sweep begins up to five times the tuning and always below half a cycle a
sample. -/
@[inline] def Drum.sweepStart (target colour : UInt32) : UInt32 :=
  let t := min target 0x08000000
  t + ((t >>> 13) * (colour % 32768))

/-- A one-pole low-pass one sample on: the state `y` moves toward the input `x` by the share `a` (Q14, up to
16384 which is all the way). With `a` at most one and the signals within 65535 nothing wraps and the result
lies between the two (`drum_one_pole_stays_between`). -/
@[inline] def Drum.onePole (y x a : Int32) : Int32 := y + (((x - y) * a) >>> 14)

/-- The high-pass: what the low-pass left of the input (`lp` is the low-pass state after this sample). -/
@[inline] def Drum.highPass (lp x : Int32) : Int32 := x - lp

/-- A square at a phase: 5461 or -5461, so six of them sum within 32767. -/
@[inline] def Drum.square (phase : UInt32) : Int32 := if phase >>> 31 = 1 then -5461 else 5461

/-- The 808's metal: six squares summed. -/
@[inline] def Drum.metal (p1 p2 p3 p4 p5 p6 : UInt32) : Int32 :=
  Drum.square p1 + Drum.square p2 + Drum.square p3 + Drum.square p4 + Drum.square p5 + Drum.square p6

/-- An envelope (Q24) through a level (Q13) into a gain (Q13, at most the level). -/
@[inline] def Drum.gain (env level : UInt32) : UInt32 := ((env >>> 9) * level) >>> 15

/-- A signal through a gain (Q13): for a signal within 65535 and a gain up to 32767 nothing wraps. -/
@[inline] def Drum.scale (x : Int32) (gain : UInt32) : Int32 := (x * gain.toInt32) >>> 13

/-- The mix as a 16-bit sample, held at full scale. -/
@[inline] def Drum.saturate (x : Int32) : Int16 := Fm.saturate x

/-- A sample older: the clap's age since its strike, held at 65535 so a long tail cannot come round to a
new burst. -/
@[inline] def Drum.ageStep (age : UInt32) : UInt32 := if age < 65535 then age + 1 else age

/-- The clap's bursts: 441 samples (10 ms) apart. -/
@[inline] def Drum.clapSpacing : UInt32 := 441

/-- Does the clap's burst envelope restart at this age? At the second and third burst (the first is the
strike). -/
@[inline] def Drum.clapRetrigger (age : UInt32) : Bool :=
  age = Drum.clapSpacing || age = 2 * Drum.clapSpacing

/-! The knobs. TIMBRE stretches every decay: 16384 is the shape's own rate, 0 four times faster, 32767
four times slower. COLOUR is the tone: the sweep's depth for the kick and toms (`Drum.sweepStart`), the
noise's share for the snare (`Drum.level`, `Drum.secondLevel`), the band's position for the clap, the metals
and the cowbell (`Drum.band`). -/

/-- The decay stretch for a timbre, Q14: 65536 (four times the rate) at 0, 16384 (the rate) at 16384, 4097
(a quarter) at 32767. -/
@[inline] def Drum.stretch (timbre : UInt32) : UInt32 :=
  let t := timbre % 32768
  if t ≤ 16384 then (65536 : UInt32) - 3 * t else (16384 : UInt32) - (((t - 16384) * 3) >>> 2)

/-- A shape's rate at a timbre: the rate stretched, held below 65536 (the envelope's limit). -/
@[inline] def Drum.decay (rate timbre : UInt32) : UInt32 :=
  min ((rate * Drum.stretch timbre) >>> 14) 65535

/-- The band's high-pass coefficient for a colour, Q14: 3072 (a cutoff near 1.5 kHz) at 0, 7168 (4.0 kHz) at
16384, 11263 (8.2 kHz) at 32767. -/
@[inline] def Drum.band (colour : UInt32) : UInt32 := (3072 : UInt32) + ((colour % 32768) >>> 2)

/-! The shapes: 0 BD, 1 SD, 2 CP, 3 CH, 4 OH, 5 LT, 6 MT, 7 HT, 8 CB, 9 CY. The tuned ones (the kick, the
toms, the cowbell) take their oscillators from the pitch by a ratio (Q8) that puts them at their 808
frequency at MIDI note 36 (65.4 Hz); the others ignore the pitch and run at fixed increments. -/

/-- The body envelope's rate at the nominal timbre: BD 219 (a hundredth at 0.50 s), SD 729 (0.15 s), CP 729
(the tail), CH 2200 (50 ms), OH 270 (0.41 s), LT 365 (0.30 s), MT 437 (0.25 s), HT 547 (0.20 s), CB 547,
CY 73 (1.5 s). -/
@[inline] def Drum.rate (shape : UInt32) : UInt32 :=
  match shape % 10 with
  | 0 => 219 | 1 => 729 | 2 => 729 | 3 => 2200 | 4 => 270
  | 5 => 365 | 6 => 437 | 7 => 547 | 8 => 547 | _ => 73

/-- The second envelope's rate: the kick's click (36000, 3 ms), the snare's noise (1400, 78 ms), the clap's
burst (9500, 12 ms), the toms' noise (5500, 20 ms), the cymbal's upper band (365, 0.30 s); none for the
metals and the cowbell. -/
@[inline] def Drum.secondRate (shape : UInt32) : UInt32 :=
  match shape % 10 with
  | 0 => 36000 | 1 => 1400 | 2 => 9500 | 5 => 5500 | 6 => 5500 | 7 => 5500 | 9 => 365 | _ => 0

/-- The sweep's rate: 792 for the kick (a 30 ms time constant), 400 for the toms (60 ms), 0 elsewhere. -/
@[inline] def Drum.sweepRate (shape : UInt32) : UInt32 :=
  match shape % 10 with
  | 0 => 792 | 5 => 400 | 6 => 400 | 7 => 400 | _ => 0

/-- A tuned oscillator's ratio to the pitch, Q8: the kick at the note, the toms at 80, 120 and 165 Hz and
the cowbell's two squares at 540 and 800 Hz for note 36; 0 for an oscillator that is fixed or absent. -/
@[inline] def Drum.ratio (shape osc : UInt32) : UInt32 :=
  match shape % 10, osc with
  | 0, 0 => 256 | 5, 0 => 313 | 6, 0 => 470 | 7, 0 => 646 | 8, 0 => 2114 | 8, 1 => 3131
  | _, _ => 0

/-- A fixed oscillator's increment: the snare's sines at 180 and 330 Hz, the metal's six squares at 205.3,
304.4, 369.6, 522.7, 540 and 800 Hz (the hi-hats and the cymbal); 0 for an oscillator that is tuned or
absent. -/
@[inline] def Drum.fixedIncrement (shape osc : UInt32) : UInt32 :=
  match shape % 10, osc with
  | 1, 0 => 17530479 | 1, 1 => 32139211
  | 3, 0 => 19994485 | 3, 1 => 29645987 | 3, 2 => 35995916
  | 3, 3 => 50906562 | 3, 4 => 52591436 | 3, 5 => 77913239
  | 4, 0 => 19994485 | 4, 1 => 29645987 | 4, 2 => 35995916
  | 4, 3 => 50906562 | 4, 4 => 52591436 | 4, 5 => 77913239
  | 9, 0 => 19994485 | 9, 1 => 29645987 | 9, 2 => 35995916
  | 9, 3 => 50906562 | 9, 4 => 52591436 | 9, 5 => 77913239
  | _, _ => 0

/-- An oscillator's increment for a shape at the voice's increment: tuned by its ratio (below Nyquist, as
`Fm.increment` holds it) or fixed. -/
@[inline] def Drum.tuning (shape osc voiceInc : UInt32) : UInt32 :=
  let ratio := Drum.ratio shape osc
  if ratio = 0 then Drum.fixedIncrement shape osc else Fm.increment voiceInc ratio

/-- The body's level, Q13: the kick's and toms' sine near full scale (7168), the snare's two sines together
(3072 less the colour's share, so more colour is less tone), the clap's tail (3072), the hi-hats, lifted
three times (24576) since the band leaves little of the squares, the cowbell twice (16384), the cymbal's
lower band (12288). -/
@[inline] def Drum.level (shape colour : UInt32) : UInt32 :=
  match shape % 10 with
  | 0 => 7168 | 1 => (3072 : UInt32) - ((colour % 32768) >>> 4) | 2 => 3072 | 3 => 24576 | 4 => 24576
  | 5 => 7168 | 6 => 7168 | 7 => 7168 | 8 => 16384 | _ => 12288

/-- The second part's level, Q13: the kick's click (2048), the snare's noise (1024 plus the colour's share),
the clap's bursts (6144), the toms' noise (2048), the cymbal's upper band (12288); 0 elsewhere. -/
@[inline] def Drum.secondLevel (shape colour : UInt32) : UInt32 :=
  match shape % 10 with
  | 0 => 2048 | 1 => (1024 : UInt32) + ((colour % 32768) >>> 3) | 2 => 6144
  | 5 => 2048 | 6 => 2048 | 7 => 2048 | 9 => 12288 | _ => 0

/-- The high-pass coefficient (Q14) of a shape's band at a colour: the snare's noise at 660 Hz (1470), the
clap's band a quarter of the metals' (near 830 Hz at the nominal colour), the cowbell's an eighth (400 Hz),
the metals' and the cymbal's the band itself (4.0 kHz); 0 (no high-pass) for the kick and the toms. -/
@[inline] def Drum.highCoefficient (shape colour : UInt32) : UInt32 :=
  match shape % 10 with
  | 1 => 1470 | 2 => Drum.band colour >>> 2 | 3 => Drum.band colour | 4 => Drum.band colour
  | 8 => Drum.band colour >>> 3 | 9 => Drum.band colour | _ => 0

/-- The low-pass coefficient (Q14) after the high-pass, or on the noise for the tuned drums: the kick's click
unfiltered (16384), the toms' noise at 1.4 kHz (2963), the clap at 3.2 kHz (6000), the hi-hats at 11 kHz
(13000), the cowbell at 2 kHz (4064), the cymbal's lower band at 9.3 kHz (12000); the snare's noise has
none (0 holds the state at nothing). -/
@[inline] def Drum.lowCoefficient (shape : UInt32) : UInt32 :=
  match shape % 10 with
  | 0 => 16384 | 2 => 6000 | 3 => 13000 | 4 => 13000 | 5 => 2963 | 6 => 2963 | 7 => 2963
  | 8 => 4064 | 9 => 12000 | _ => 0

/-- The cymbal's upper band, Q14: stage 0 is its high-pass at 9.3 kHz (12000), stage 1 its low-pass at 17 kHz
(15000). -/
@[inline] def Drum.upperCoefficient (stage : UInt32) : UInt32 := if stage = 0 then 12000 else 15000
