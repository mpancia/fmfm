import Firmware.Macro

set_option compiler.extract_closed false

/-! C entry points for `Firmware/Macro.lean`: one function per result. -/

/-- `csaw`: the sample. -/
@[export fm1_macro_csaw] def macroCsaw (x shift : Int32) : Int16 := Macro.csaw x shift

/-- `morph`: the low-pass state after the sample. -/
@[export fm1_macro_morph_lp] def macroMorphLp (a b : Int32) (balance : UInt32) (lp f fuzz : Int32) : Int32 :=
  (Macro.morph a b balance lp f fuzz).lp

/-- `morph`: the sample. -/
@[export fm1_macro_morph_out] def macroMorphOut (a b : Int32) (balance : UInt32) (lp f fuzz : Int32) : Int16 :=
  (Macro.morph a b balance lp f fuzz).out

/-- `saw_square`: the sample. -/
@[export fm1_macro_saw_square] def macroSawSquare (saw square parameter : Int32) : Int16 :=
  Macro.sawSquare saw square parameter

/-- `triple`: the running sum with one oscillator added. -/
@[export fm1_macro_triple_add] def macroTripleAdd (sum x : Int32) : Int16 := Macro.tripleAdd sum x

/-- `sub`: the sample. -/
@[export fm1_macro_sub] def macroSub (a b parameter : Int32) : Int16 := Macro.sub a b parameter

/-- `dual_sync`: the sample. -/
@[export fm1_macro_dual_sync] def macroDualSync (a b parameter : Int32) : Int16 := Macro.dualSync a b parameter

/-- `sine_triangle`: the sample. -/
@[export fm1_macro_sine_triangle] def macroSineTriangle (a b parameter : Int32) : Int16 :=
  Macro.sineTriangle a b parameter

/-- `buzz`: the sample. -/
@[export fm1_macro_buzz] def macroBuzz (a b : Int32) : Int16 := Macro.buzz a b
