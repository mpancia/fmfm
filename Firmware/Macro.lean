import Firmware.Digital

set_option compiler.extract_closed false

/-!
# Macro oscillator mixing, one sample at a time

Port of the sample-combining arithmetic of Braids' `macro_oscillator.cc` (Emilie Gillet, MIT): how the buffers
filled by the analog oscillators (themselves Lean, `Firmware/Analog.lean`) are mixed. Loops and parameter
smoothing are in `voices/macro_glue.c`. Lean shifts bind tighter than `*` and `+`, so shifted products are
parenthesized.
-/

/-- One entry of Braids' violent-overdrive wave shaper (257 entries), looked up by C. Trusted data. -/
@[extern "fm1_braids_ws_violent_overdrive"] opaque Macro.violentTable (index : UInt32) : Int16

/-- A parameter (0 to 32767) as a 16-bit crossfade balance: twice its value. -/
@[inline] def Macro.balance (parameter : Int32) : UInt32 := (parameter <<< 1).toUInt32 &&& 0xFFFF

/-- CSAW: the saw shifted by `shift` and gained by 13/8. -/
@[inline] def Macro.csaw (x shift : Int32) : Int16 := (((x + shift) * 13) >>> 3).toInt16

/-- The result of one morph sample: the low-pass state and the sample. -/
structure MorphStep where
  lp : Int32
  out : Int16

/-- Morph: the two oscillators crossfaded by `balance`, low-passed by `f`, driven through the violent overdrive,
and blended with the clean mix by `fuzz`. -/
@[inline] def Macro.morph (a b : Int32) (balance : UInt32) (lp f fuzz : Int32) : MorphStep :=
  let sample := Digital.mix a b balance
  let lp' := Digital.clip (lp + (((sample - lp) * f) >>> 15))
  let fuzzed := Analog.shape Macro.violentTable (lp' + 32768).toUInt32
  { lp := lp', out := (Digital.mix sample fuzzed (fuzz.toUInt32 &&& 0xFFFF)).toInt16 }

/-- Saw + square: the square at 148/256, crossfaded in by the parameter. -/
@[inline] def Macro.sawSquare (saw square parameter : Int32) : Int16 :=
  (Digital.mix saw (((square * 148) >>> 8).toInt16.toInt32) (Macro.balance parameter)).toInt16

/-- Triple: one of the three oscillators, at 21/64, added to the running sum. -/
@[inline] def Macro.tripleAdd (sum x : Int32) : Int16 := (sum + ((x * 21) >>> 6)).toInt16

/-- Sub: the sub-oscillator fades in toward both ends of the parameter's range. -/
@[inline] def Macro.sub (a b parameter : Int32) : Int16 :=
  let gain := if parameter < 16384 then 16383 - parameter else parameter - 16384
  (Digital.mix a b (Macro.balance gain)).toInt16

/-- Dual sync: the master and the synced oscillator crossfaded, at three quarters. -/
@[inline] def Macro.dualSync (a b parameter : Int32) : Int16 :=
  (((Digital.mix a b (Macro.balance parameter)) >>> 2) * 3).toInt16

/-- Sine + triangle: the two folded waves crossfaded. -/
@[inline] def Macro.sineTriangle (a b parameter : Int32) : Int16 :=
  (Digital.mix a b (Macro.balance parameter)).toInt16

/-- Buzz: the mean of two buzzes. -/
@[inline] def Macro.buzz (a b : Int32) : Int16 := ((a >>> 1) + (b >>> 1)).toInt16
