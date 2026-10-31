import Firmware.Digital

set_option compiler.extract_closed false

/-!
# Vowels and the question mark, one sample at a time

Port of the vowel, vowel (FOF) and question-mark engines of Braids (`digital_oscillator.cc`, Emilie Gillet, MIT).
Like `Firmware/Digital.lean`: pure scalar functions, one result structure each, every field exported on its own by
`Firmware/VowelsApi.lean`. The per-formant state, the buffers and the random numbers live in
`voices/vowels_glue.c`, which loads the state, calls these and stores the results. Lean shifts bind tighter than
`*` and `+`, so shifted products are parenthesized.
-/

/-- One entry of Braids' formant sine table (256 entries: 16 phases by 16 amplitudes), looked up by C. Trusted data. -/
@[extern "fm1_braids_formant_sine"] opaque Vowels.formantSine (index : UInt32) : Int16

/-- One entry of Braids' formant square table (256 entries), looked up by C. Trusted data. -/
@[extern "fm1_braids_formant_square"] opaque Vowels.formantSquare (index : UInt32) : Int16

/-- One byte of Braids' Morse-like code table (`wt_code`), looked up by C. Trusted data. -/
@[extern "fm1_braids_vowels_wt_code"] opaque Vowels.codeTable (index : UInt32) : UInt8

/-- The result of one vowel sample: the pitch phase, the three formant phases and the sample. -/
structure Vowels.VowelStep where
  phase : UInt32
  formant0 : UInt32
  formant1 : UInt32
  formant2 : UInt32
  out : Int16

/-- The vowel: three formants (two sines and a square, each a table of 16 phases by 16 amplitudes) run at their
own rates and amplitudes, cut off by a falling ramp of the pitch phase so that they restart on every cycle, then
soft-clipped. `noise` (0 for a vowel, 4095 for a noisy consonant) jitters the instant of the restart by the random
number `random`. -/
@[inline] def Vowels.vowel (phase inc : UInt32) (f0 f1 f2 : UInt32) (inc0 inc1 inc2 : UInt32)
    (amp0 amp1 amp2 : UInt32) (noise random : Int32) : Vowels.VowelStep :=
  let p := phase + inc
  let q0 := f0 + inc0
  let q1 := f1 + inc1
  let q2 := f2 + inc2
  let s0 := (Vowels.formantSine (((q0 >>> 24) &&& 0xF0) ||| amp0)).toInt32
  let s1 := (s0 + (Vowels.formantSine (((q1 >>> 24) &&& 0xF0) ||| amp1)).toInt32).toInt16.toInt32
  let s2 := (s1 + (Vowels.formantSquare (((q2 >>> 24) &&& 0xF0) ||| amp2)).toInt32).toInt16.toInt32
  let s3 := (s2 * ((255 : UInt32) - (p >>> 24)).toInt32).toInt16.toInt32
  let restart := (p + (random * noise).toUInt32) < inc
  let s4 := if restart then 0 else s3
  let shaped := Analog.shape Digital.overdriveTable ((s4 + 32768) &&& 0xFFFF).toUInt32
  { phase := p, formant0 := if restart then 0 else q0, formant1 := if restart then 0 else q1,
    formant2 := if restart then 0 else q2, out := shaped.toInt16 }

/-- The result of the ramp generator of the FOF vowel: the phase, this sample and the part carried to the next. -/
structure Vowels.FofSawStep where
  phase : UInt32
  here : Int32
  next : Int32

/-- The band-limited saw that excites the formant filters, at twice the rate (`inc` is double the pitch
increment). When the phase wraps, a parabolic correction is split between this sample and the next. `next` is the
share carried from the last sample. -/
@[inline] def Vowels.fofSaw (phase inc : UInt32) (next : Int32) : Vowels.FofSawStep :=
  let p := phase + inc
  let wrapped := p < inc
  let t := if wrapped then (let t0 := p / (inc >>> 16); if t0 > 65535 then 65535 else t0) else 0
  let u := if wrapped then 65535 - t else 0
  { phase := p, here := next - ((t * t) >>> 18).toInt32,
    next := ((u * u) >>> 18).toInt32 + (p >>> 17).toInt32 }

/-- The result of one filter of the formant bank: the low-pass and band-pass states and the filter's share of
the output. -/
structure Vowels.FofFilterStep where
  lp : Int32
  bp : Int32
  contribution : Int32

/-- One state-variable filter of the bank of five, fed the saw `input`. `f` is its frequency coefficient and `amp`
the amplitude (Braids uses the first formant's amplitude for all five). -/
@[inline] def Vowels.fofFilter (lp bp f amp input : Int32) : Vowels.FofFilterStep :=
  let notch := input - (bp >>> 6)
  let lp' := Digital.clip (lp + ((f * bp) >>> 15))
  let hp := notch - lp'
  let bp' := Digital.clip (bp + ((f * hp) >>> 15))
  { lp := lp', bp := bp', contribution := (bp' * amp) >>> 17 }

/-- The result of the end of an FOF vowel step: the interpolated sample, then the sample itself. -/
structure Vowels.FofOutStep where
  mid : Int16
  out : Int16

/-- The sum of the five filters, clipped, as two output samples: the average with the last one, then itself. -/
@[inline] def Vowels.fofOut (sum previous : Int32) : Vowels.FofOutStep :=
  let out := Digital.clip sum
  { mid := ((out + previous) >>> 1).toInt16, out := out.toInt16 }

/-- The result of one question-mark sample. -/
structure Vowels.QuestionStep where
  phase : UInt32
  cycle : UInt32
  cycleIndex : UInt32
  on : Bool
  seed : Int32
  length : Int16
  out : Int16

/-- The question mark's distortion term: a square-law of the sample, scaled by `parameter` (0 to 32767). -/
@[inline] def Vowels.questionDrive (sample parameter : Int32) : Int32 :=
  (((sample * sample) >>> 14) * parameter) >>> 15

/-- The question mark: a sine that a stream of dits and dahs (read two bits at a time from the code table) turns on
and off, with noise from a wandering seed on top, then distorted. `dit` is the length of a dit in samples, `threshold`
the floor of the noise and `parameter` the distortion; `r1` and `r2` are two consecutive random numbers. -/
@[inline] def Vowels.question (phase inc cycle cycleIndex : UInt32) (on : Bool) (seed : Int32) (length : Int16)
    (dit : UInt32) (threshold parameter r1 r2 : Int32) : Vowels.QuestionStep :=
  let p0 := phase + inc
  let tone : Int32 := if on then (Analog.sineAt p0 * 3) >>> 2 else 0
  let c1 := cycle + 1
  let tick := c1 > dit
  let l1 : Int16 := if tick then length - 1 else length
  let hit := tick && l1 == 0
  let index1 := cycleIndex + 1
  let code : UInt32 := if hit then (Vowels.codeTable (index1 >>> 2)).toUInt32 else 0
  let span : UInt32 := ((2 : UInt32) <<< ((code >>> ((index1 &&& 3) <<< 1)) &&& 3)) - 1
  let stop := hit && span == 15
  let length' : Int16 := if hit then (if stop then 100 else span.toUInt16.toInt16) else l1
  let on' : Bool := if hit then (if stop then false else !on) else on
  let cycleIndex' : UInt32 := if hit then (if stop then 0xFFFFFFFF else index1) else cycleIndex
  let p1 : UInt32 := if hit then 0x40000000 else p0
  let cycle' : UInt32 := if tick then 0 else c1
  let seed' := seed + (r1 >>> 2)
  let level0 := seed' >>> 8
  let level1 := if level0 < 0 then 0 - level0 else level0
  let level2 := if level1 < threshold then threshold else level1
  let level3 := if level2 > 16000 then 16000 else level2
  let noise0 := (r2 * level3) >>> 15
  let noise1 := (noise0 * (Analog.sineTable ((p1 >>> 22) &&& 0xFF)).toInt32) >>> 15
  let s1 := Digital.clip (tone + noise1)
  let s2 := Digital.clip (s1 + Vowels.questionDrive s1 parameter)
  { phase := p1, cycle := cycle', cycleIndex := cycleIndex', on := on', seed := seed', length := length',
    out := s2.toInt16 }
