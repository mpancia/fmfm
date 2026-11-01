set_option compiler.extract_closed false

/-!
The per-block setup of Braids' analog oscillator (`AnalogOscillator::Render*` in
`voices/braids/analog_oscillator.cc`): the pitch clamp, the pulse widths of the square and the variable saw,
and the comb zones and crossfade of the buzz. A pitch is a MIDI note in 1/128 semitones; a parameter is 0 to
32767. One scalar per definition; the C++ calls each once per block.
-/

namespace AnalogSetup

/-- The pitch held between 0 and note 128. The phase step is taken from the pitch before this clamp; the
buzz's zone is taken after it. -/
@[inline] def clampedPitch (pitch : Int16) : Int16 :=
  if pitch > 16384 then 16384 else if pitch < 0 then 0 else pitch

/-- The square's parameter, held at or below 32000 so the pulse keeps some width. -/
@[inline] def squareParameter (parameter : Int16) : Int32 :=
  if parameter > 32000 then 32000 else parameter.toInt32

/-- The phase where the square's pulse turns on: `(32768 - parameter) << 16`. -/
@[inline] def squarePulseWidth (parameter : Int16) : UInt32 :=
  (32768 - squareParameter parameter).toUInt32 <<< 16

/-- The phase where the variable saw's second slope starts: the parameter, at least 1024, as a phase. -/
@[inline] def variableSawPulseWidth (parameter : Int16) : UInt32 :=
  (if parameter < 1024 then (1024 : Int32) else parameter.toInt32).toUInt32 <<< 16

/-- The buzz's pitch raised by half the parameter's complement: a lower parameter reads a brighter comb. -/
@[inline] def buzzShiftedPitch (pitch parameter : Int16) : Int32 :=
  pitch.toInt32 + ((32767 - parameter.toInt32) >>> 1)

/-- Which of the 15 comb zones the buzz reads, held at the last one. -/
@[inline] def buzzZone (pitch parameter : Int16) : UInt32 :=
  let zone := (buzzShiftedPitch pitch parameter >>> 10).toUInt32
  if zone ≥ 15 then 14 else zone

/-- The zone the buzz crossfades towards: the one after `buzzZone`, held at the last one. -/
@[inline] def buzzZone2 (pitch parameter : Int16) : UInt32 :=
  let next := buzzZone pitch parameter + 1
  if next ≥ 15 then 14 else next

/-- How far the buzz has moved from its zone to the next, as a 16-bit crossfade. -/
@[inline] def buzzCrossfade (pitch parameter : Int16) : UInt32 :=
  (buzzShiftedPitch pitch parameter <<< 6).toUInt32 &&& 0xFFFF

end AnalogSetup
