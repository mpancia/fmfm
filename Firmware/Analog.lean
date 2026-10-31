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
  /-- The CSAW's jump depth; unused by the other oscillators. -/
  depth : Int32 := 0

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

/-- A triangle wave at `phase`, from -32768 to 32767. -/
@[inline] def Analog.triangleWave (phase : UInt32) : Int32 :=
  let p16 := phase >>> 16
  let folded := (((p16 <<< 1) ^^^ (if p16 &&& 0x8000 != 0 then 0xFFFF else 0)) &&& 0xFFFF) ^^^ 0x8000
  if folded ≥ 0x8000 then folded.toInt32 - 65536 else folded.toInt32

/-- One half of a triangle step: the wave at `phase`, halved, from -16384 to 16383. -/
@[inline] def Analog.triangleHalf (phase : UInt32) : Int32 := Analog.triangleWave phase >>> 1

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

/-- Which entry of a 257-entry table a 32-bit phase falls on: its top 8 bits. The entry after it is blended in. -/
@[inline] def Analog.tableIndex (phase : UInt32) : UInt32 := phase >>> 24

/-- The sine table at a phase, with the two nearest entries blended. -/
@[inline] def Analog.sineAt (phase : UInt32) : Int32 :=
  let a := (Analog.sineTable (Analog.tableIndex phase)).toInt32
  let b := (Analog.sineTable (Analog.tableIndex phase + 1)).toInt32
  (a + (((b - a) * ((phase >>> 8) &&& 0xFFFF).toInt32) >>> 16)).toInt16.toInt32

/-- A sine wave. `syncIn` non-zero restarts the cycle. -/
@[inline] def Analog.sine (phase inc : UInt32) (syncIn : UInt8) : Step :=
  let p := if syncIn != 0 then 0 else phase + inc
  { phase := p, next := 0, high := false, out := (Analog.sineAt p).toInt16, syncOut := 0 }

/-- One entry of Braids' sine-fold table (257 entries), looked up by C. Trusted data, like `sineTable`. -/
@[extern "fm1_braids_ws_sine_fold"] opaque Analog.sineFoldTable (index : UInt32) : Int16

/-- One entry of Braids' triangle-fold table (257 entries), looked up by C. Trusted data. -/
@[extern "fm1_braids_ws_tri_fold"] opaque Analog.triFoldTable (index : UInt32) : Int16

/-- One entry of one of Braids' 15 band-limited comb tables (257 entries each), looked up by C. Trusted data. -/
@[extern "fm1_braids_comb"] opaque Analog.combTable (zone index : UInt32) : Int16

/-- Blend two neighbouring entries of a table of 257 values, by an 8-bit fraction (Braids' `Interpolate88`, which returns a 16-bit value). -/
@[inline] def Analog.blend88 (a b : Int32) (index : UInt32) : Int32 :=
  (a + (((b - a) * (index &&& 0xFF).toInt32) >>> 8)).toInt16.toInt32

/-- Which entry of a 257-entry wave shaper a 16-bit index falls on: its top 8 bits. -/
@[inline] def Analog.shapeIndex (index : UInt32) : UInt32 := index >>> 8

/-- The wave-shaper table at a 16-bit index (Braids' `Interpolate88`). -/
@[inline] def Analog.shape (table : UInt32 → Int16) (index : UInt32) : Int32 :=
  Analog.blend88 (table (Analog.shapeIndex index)).toInt32 (table (Analog.shapeIndex index + 1)).toInt32 index

/-- The drive of a wave folder: 2048 plus the parameter (0 to 32767) scaled up to 30720. -/
@[inline] def Analog.foldGain (parameter : Int32) : Int32 :=
  ((2048 : Int32) + ((parameter * 30720) >>> 15)).toInt16.toInt32

/-- One half step of a wave folder: `wave` (a signed 16-bit value) driven by `gain`, then folded by `table`. -/
@[inline] def Analog.fold (table : UInt32 → Int16) (wave gain : Int32) : Int32 :=
  let driven := ((wave * gain) >>> 15).toInt16.toInt32
  Analog.shape table ((driven + 32768) &&& 0xFFFF).toUInt32 >>> 1

/-- A triangle run through a wave folder (computed at twice the rate and averaged). `parameter` 0 to 32767 is
how hard the wave is driven into the folds. -/
@[inline] def Analog.triangleFold (phase inc : UInt32) (parameter : Int32) (syncIn : UInt8) : Step :=
  let start := if syncIn != 0 then 0 else phase
  let gain := Analog.foldGain parameter
  let p1 := start + (inc >>> 1)
  let p2 := p1 + (inc >>> 1)
  { phase := p2, next := 0, high := false, syncOut := 0,
    out := (Analog.fold Analog.triFoldTable (Analog.triangleWave p1) gain +
      Analog.fold Analog.triFoldTable (Analog.triangleWave p2) gain).toInt16 }

/-- A sine run through a wave folder (computed at twice the rate and averaged). -/
@[inline] def Analog.sineFold (phase inc : UInt32) (parameter : Int32) (syncIn : UInt8) : Step :=
  let start := if syncIn != 0 then 0 else phase
  let gain := Analog.foldGain parameter
  let p1 := start + (inc >>> 1)
  let p2 := p1 + (inc >>> 1)
  { phase := p2, next := 0, high := false, syncOut := 0,
    out := (Analog.fold Analog.sineFoldTable (Analog.sineAt p1) gain +
      Analog.fold Analog.sineFoldTable (Analog.sineAt p2) gain).toInt16 }

/-- A buzz: two band-limited comb tables (`zone` and `zone2`, usually neighbours) crossfaded by `crossfade`. -/
@[inline] def Analog.buzz (phase inc zone zone2 crossfade : UInt32) (syncIn : UInt8) : Step :=
  let p := if syncIn != 0 then 0 else phase + inc
  let a := (Analog.combTable zone (Analog.tableIndex p)).toInt32
  let a1 := (Analog.combTable zone (Analog.tableIndex p + 1)).toInt32
  let b := (Analog.combTable zone2 (Analog.tableIndex p)).toInt32
  let b1 := (Analog.combTable zone2 (Analog.tableIndex p + 1)).toInt32
  let fraction := ((p >>> 8) &&& 0xFFFF).toInt32
  let x := (a + (((a1 - a) * fraction) >>> 16)).toInt16.toInt32
  let y := (b + (((b1 - b) * fraction) >>> 16)).toInt16.toInt32
  { phase := p, next := 0, high := false, syncOut := 0,
    out := (x + (((y - x) * (crossfade &&& 0xFFFF).toInt32) >>> 16)).toInt16 }

/-- The saw with a movable break point: a ramp that jumps down at `pw` and again at the wrap, `pw` set by the
parameter. Edges are corrected at half strength each. -/
@[inline] def Analog.variableSaw (phase inc pw : UInt32) (next : Int32) (high : Bool) (syncIn : UInt8) : Step :=
  let den := inc >>> 16
  let syncReset := syncIn != 0
  let resetTime := Analog.resetTime syncIn
  let phaseAtReset := phase + (65535 - resetTime) * den
  let transition := syncReset && (phaseAtReset < phase || (!high && phaseAtReset ≥ pw))
  let before := (phaseAtReset >>> 18).toInt32 + ((phaseAtReset - pw) >>> 18).toInt32
  let afterReset := ((0 - pw) >>> 18).toInt32
  let jump := afterReset - before
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
  let here := (if syncReset then next + ((jump * Analog.thisBlep resetTime) >>> 15) else next) -
    (if rise1 then Analog.thisBlep t1 >>> 1 else 0) - (if fall then Analog.thisBlep t2 >>> 1 else 0) -
    (if rise2 then Analog.thisBlep t3 >>> 1 else 0)
  let after := (if syncReset then (jump * Analog.nextBlep resetTime) >>> 15 else 0) -
    (if rise1 then Analog.nextBlep t1 >>> 1 else 0) - (if fall then Analog.nextBlep t2 >>> 1 else 0) -
    (if rise2 then Analog.nextBlep t3 >>> 1 else 0)
  let phase2 := if syncReset then resetTime * den else phase1
  let high2 := !syncReset && (if fall then rise2 else high1)
  { phase := phase2, next := after + (phase2 >>> 18).toInt32 + ((phase2 - pw) >>> 18).toInt32, high := high2,
    out := ((here - 16384) <<< 1).toInt16, syncOut := Analog.syncOut phase1 inc }

/-- What the CSAW remembers besides its phase: how deep the jump at the break point goes. -/
@[inline] def Analog.csawDepth (aux : Int32) : Int32 := ((-2048 : Int32) + (aux >>> 2)).toInt16.toInt32

/-- The jump an edge makes, as a 16-bit value (the C++ keeps it in an `int16_t`). -/
@[inline] def Analog.jump16 (after before : Int32) : Int32 := (after - before).toInt16.toInt32

/-- The CSAW: a ramp that jumps to `depth` at `pw`, then ramps on. `aux` sets the depth after each wrap; the new
depth comes back in the step. -/
@[inline] def Analog.csaw (phase inc pw : UInt32) (next depth aux : Int32) (high : Bool) (syncIn : UInt8) : Step :=
  let den := inc >>> 16
  let syncReset := syncIn != 0
  let resetTime := Analog.resetTime syncIn
  let phaseAtReset := phase + (65535 - resetTime) * den
  let transition := syncReset && (phaseAtReset < phase || (!high && phaseAtReset ≥ pw))
  let atReset := syncReset && phase ≥ pw
  let depth0 := if atReset then Analog.csawDepth aux else depth
  let jumpReset := Analog.jump16 depth0 (phaseAtReset >>> 18).toInt32
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
  let depth1 := if fall then Analog.csawDepth aux else depth0
  let jump1 := Analog.jump16 (phase1 >>> 18).toInt32 depth0
  let jump2 := Analog.jump16 depth1 16383
  let jump3 := Analog.jump16 (phase1 >>> 18).toInt32 depth1
  let here := (if atReset then next + ((jumpReset * Analog.thisBlep resetTime) >>> 15) else next) +
    (if rise1 then (jump1 * Analog.thisBlep t1) >>> 15 else 0) +
    (if fall then (jump2 * Analog.thisBlep t2) >>> 15 else 0) +
    (if rise2 then (jump3 * Analog.thisBlep t3) >>> 15 else 0)
  let after := (if atReset then (jumpReset * Analog.nextBlep resetTime) >>> 15 else 0) +
    (if rise1 then (jump1 * Analog.nextBlep t1) >>> 15 else 0) +
    (if fall then (jump2 * Analog.nextBlep t2) >>> 15 else 0) +
    (if rise2 then (jump3 * Analog.nextBlep t3) >>> 15 else 0)
  let phase2 := if syncReset then resetTime * den else phase1
  let high2 := !syncReset && (if fall then rise2 else high1)
  { phase := phase2, next := after + (if phase2 < pw then depth1 else (phase2 >>> 18).toInt32), high := high2,
    out := ((here - 8192) <<< 1).toInt16, syncOut := Analog.syncOut phase1 inc, depth := depth1 }
