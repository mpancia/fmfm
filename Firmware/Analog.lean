set_option compiler.extract_closed false

/-!
# Analog oscillators, one sample at a time

Port of the oscillators in Mutable Instruments' Braids (`analog_oscillator.cc`, Emilie Gillet, MIT): saw,
square, triangle and sine. Each function does the arithmetic of one sample and returns a `Step`. The C side
(`voices/analog_glue.c`) owns the buffers and the loop; each result field is exported on its own, so that a
call needs no allocation and can run in the audio interrupt.

Numbers are 32-bit and wrap, as the C++ does. Unlike C, Lean's shifts bind tighter than `*` and `+`, so every
shifted product or sum is parenthesized. A phase is a position in a cycle, with 2^32 the whole cycle.
`next` is the part of a step edge that falls into the following sample. Division by a zero step gives 0 here;
the C++ would trap, and the engine never gets there because the step is above 65536 for any audible pitch.
-/

/-- The result of one sample. -/
structure Step where
  phase : UInt32
  next : Int32
  high : Bool
  out : Int16
  syncOut : UInt8

/-- The correction for an edge `t / 65536` of a sample after the sample began, for this sample. -/
@[inline] def Analog.thisBlep (t : UInt32) : Int32 :=
  let t := if t > 65535 then 65535 else t
  ((t * t) >>> 18).toInt32

/-- The correction for the same edge, for the next sample. -/
@[inline] def Analog.nextBlep (t : UInt32) : Int32 :=
  let t := 65535 - (if t > 65535 then 65535 else t)
  (0 : Int32) - ((t * t) >>> 18).toInt32

/-- The moment a saw or square cycle ended, as the sync output tells the other oscillator: where in this
sample the phase wrapped, 1 to 255. 0 means it did not wrap. -/
@[inline] def Analog.syncOut (phase inc : UInt32) : UInt8 :=
  if phase < inc then (phase / (inc >>> 7) + 1).toUInt8 else 0

/-- Where a sync pulse landed in this sample, from the sync input byte (0 means no pulse). -/
@[inline] def Analog.resetTime (syncIn : UInt8) : UInt32 := (syncIn.toUInt32 - 1) <<< 9

/-- A band-limited saw. `syncIn` is 0 or a pulse position from another oscillator (1 to 255) that restarts
the cycle. -/
@[inline] def Analog.saw (phase inc : UInt32) (next : Int32) (syncIn : UInt8) : Step :=
  let den := inc >>> 16
  let syncReset := syncIn != 0
  let resetTime := Analog.resetTime syncIn
  let phaseAtReset := phase + (65535 - resetTime) * den
  let transition := phaseAtReset < phase
  let discontinuity := (phaseAtReset >>> 17).toInt32
  let here := if syncReset then next - ((discontinuity * Analog.thisBlep resetTime) >>> 15) else next
  let after := if syncReset then (0 : Int32) - ((discontinuity * Analog.nextBlep resetTime) >>> 15) else 0
  let phase1 := phase + inc
  let wrapped := phase1 < inc
  let edge := (transition || !syncReset) && wrapped
  let t := if edge then phase1 / den else 0
  let here := if edge then here - Analog.thisBlep t else here
  let after := if edge then after - Analog.nextBlep t else after
  let phase2 := if syncReset then resetTime * den else phase1
  { phase := phase2, next := after + (phase2 >>> 17).toInt32, high := false,
    out := ((here - 16384) <<< 1).toInt16, syncOut := Analog.syncOut phase1 inc }

/-- A band-limited pulse wave. `pw` is the phase where the pulse turns on (`(32768 - width) << 16`).

Within one sample the output can rise at the pulse width, fall at the wrap, and, if it fell, rise again: the
three edges of the C++ loop, which never runs a fourth pass. Each edge adds its correction to this sample and
the next. -/
@[inline] def Analog.square (phase inc pw : UInt32) (next : Int32) (high : Bool) (syncIn : UInt8) : Step :=
  let den := inc >>> 16
  let syncReset := syncIn != 0
  let resetTime := Analog.resetTime syncIn
  let phaseAtReset := phase + (65535 - resetTime) * den
  let transition := syncReset && (phaseAtReset < phase || (!high && phaseAtReset ≥ pw))
  let atReset := syncReset && phaseAtReset ≥ pw
  let phase1 := phase + inc
  let wrapped := phase1 < inc
  let loops := transition || !syncReset
  let rise1 := loops && !high && phase1 ≥ pw
  let high1 := high || rise1
  let fall := loops && high1 && wrapped
  let rise2 := fall && phase1 ≥ pw
  let t1 := if rise1 then (phase1 - pw) / den else 0
  let t2 := if fall then phase1 / den else 0
  let t3 := if rise2 then (phase1 - pw) / den else 0
  let here := (if atReset then next - Analog.thisBlep resetTime else next) +
    (if rise1 then Analog.thisBlep t1 else 0) - (if fall then Analog.thisBlep t2 else 0) +
    (if rise2 then Analog.thisBlep t3 else 0)
  let after := (if atReset then (0 : Int32) - Analog.nextBlep resetTime else 0) +
    (if rise1 then Analog.nextBlep t1 else 0) - (if fall then Analog.nextBlep t2 else 0) +
    (if rise2 then Analog.nextBlep t3 else 0)
  let phase2 := if syncReset then resetTime * den else phase1
  let high2 := !syncReset && (if fall then rise2 else high1)
  { phase := phase2, next := after + (if phase2 < pw then 0 else 32767), high := high2,
    out := ((here - 16384) <<< 1).toInt16, syncOut := Analog.syncOut phase1 inc }

/-- One half of a triangle step: the wave at `phase`, from -16384 to 16383. -/
@[inline] def Analog.triangleHalf (phase : UInt32) : Int32 :=
  let p16 := phase >>> 16
  let folded := (((p16 <<< 1) ^^^ (if p16 &&& 0x8000 != 0 then 0xFFFF else 0)) &&& 0xFFFF) ^^^ 0x8000
  let signed : Int32 := if folded ≥ 0x8000 then folded.toInt32 - 65536 else folded.toInt32
  signed >>> 1

/-- A triangle wave, computed at twice the rate and averaged. `syncIn` non-zero restarts the cycle. -/
@[inline] def Analog.triangle (phase inc : UInt32) (syncIn : UInt8) : Step :=
  let start := if syncIn != 0 then 0 else phase
  let p1 := start + (inc >>> 1)
  let p2 := p1 + (inc >>> 1)
  { phase := p2, next := 0, high := false, out := (Analog.triangleHalf p1 + Analog.triangleHalf p2).toInt16,
    syncOut := 0 }

/-- One entry of Braids' sine table (257 entries, one period, in `voices/braids/resources.cc`), looked up by
C. This is trusted: the table is data, and the contract is only that it is that table. -/
@[extern "fm1_braids_wav_sine"] opaque Analog.sineTable (index : UInt32) : Int16

/-- The sine table at a phase, with the two nearest entries blended. -/
@[inline] def Analog.sineAt (phase : UInt32) : Int32 :=
  let a := (Analog.sineTable (phase >>> 24)).toInt32
  let b := (Analog.sineTable ((phase >>> 24) + 1)).toInt32
  a + (((b - a) * ((phase >>> 8) &&& 0xFFFF).toInt32) >>> 16)

/-- A sine wave. `syncIn` non-zero restarts the cycle. -/
@[inline] def Analog.sine (phase inc : UInt32) (syncIn : UInt8) : Step :=
  let p := if syncIn != 0 then 0 else phase + inc
  { phase := p, next := 0, high := false, out := (Analog.sineAt p).toInt16, syncOut := 0 }
