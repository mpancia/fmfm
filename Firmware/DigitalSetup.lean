import Firmware.Pitch

set_option compiler.extract_closed false

/-!
The per-block setup of Braids' digital oscillator for the FM, ring modulator, toy and digital modulation
engines, and its `ComputeDelay` (`voices/braids/digital_oscillator.cc`): the pitch and the two parameters of a
block become the phase steps, the attenuation and the decimation the sample code runs with. A pitch is a MIDI
note in 1/128 semitones; a parameter is 0 to 32767. Each offset pitch is cut to 16 bits before the step is
looked up, as the C++ does when it passes an `int` to `ComputePhaseIncrement(int16_t)`. Scalar only.
-/

namespace DigitalSetup

/-- One entry of Braids' 129-entry table that snaps the FM ratio parameter to musical intervals
(`lut_fm_frequency_quantizer` in `voices/braids/resources.cc`), looked up by C. Trusted data. -/
@[extern "fm1_braids_lut_fm_frequency_quantizer"] opaque fmQuantizerTable (index : UInt32) : UInt16

/-- One entry of Braids' 97-entry table of delay-line lengths for the top octave, in samples as a 16.16
fraction (`lut_oscillator_delays`), looked up by C. Trusted data. -/
@[extern "fm1_braids_lut_oscillator_delays"] opaque delayTable (index : UInt32) : UInt32

/-- Which quantizer entry the FM ratio parameter falls on: its high byte. The entry after it is blended in. -/
@[inline] def fmQuantizerIndex (param : Int16) : UInt32 := (param.toInt32 >>> 8).toUInt32 &&& 0xFFFF

/-- The FM ratio parameter snapped to the quantizer table, the two nearest entries blended by its low byte.
The result replaces the parameter for the block. -/
@[inline] def fmQuantizedParameter (param : Int16) : Int16 :=
  let a := (fmQuantizerTable (fmQuantizerIndex param)).toInt16.toInt32
  let b := (fmQuantizerTable (fmQuantizerIndex param + 1)).toInt16.toInt32
  (a + (((b - a) * (param.toInt32 &&& 255)) >>> 8)).toInt16

/-- The FM modulator's pitch: an octave above the carrier, detuned by the quantized ratio parameter. -/
@[inline] def fmModulatorPitch (pitch param : Int16) : Int16 :=
  ((1536 : Int32) + pitch.toInt32 + ((param.toInt32 - 16384) >>> 1)).toInt16

/-- The FM modulator's phase step, halved: the sample code runs the modulator at half rate. -/
@[inline] def fmModulatorIncrement (pitch param : Int16) : UInt32 :=
  Pitch.phaseIncrement (fmModulatorPitch pitch param) >>> 1

/-- How much the feedback FM attenuates its feedback, 0 to 32767: less the higher the modulator sits above
note 72. -/
@[inline] def feedbackAttenuation (pitch param : Int16) : Int32 :=
  let above := pitch.toInt32 - (9216 : Int32) + ((param.toInt32 - 16384) >>> 1)
  let attenuation := (32767 : Int32) - above * 4
  if attenuation < 0 then 0 else if attenuation > 32767 then 32767 else attenuation

/-- The pitch of one of the ring modulator's two modulators: the carrier detuned by a parameter. -/
@[inline] def ringPitch (pitch param : Int16) : Int16 :=
  (pitch.toInt32 + ((param.toInt32 - 16384) >>> 2)).toInt16

/-- The phase step of one of the ring modulator's two modulators. -/
@[inline] def ringIncrement (pitch param : Int16) : UInt32 := Pitch.phaseIncrement (ringPitch pitch param)

/-- The toy's phase step: the block's step at a quarter, since the toy runs four times oversampled. -/
@[inline] def toyIncrement (increment : UInt32) : UInt32 := increment >>> 2

/-- How many samples the toy holds each one, 1 to 512, from the first parameter. -/
@[inline] def toyDecimation (param : Int16) : UInt16 :=
  ((512 : Int32) - (param.toInt32 >>> 6)).toUInt32.toUInt16

/-- How many low bits the toy drops, 0 to 127, from the second parameter. -/
@[inline] def toyBits (param : Int16) : UInt8 := (param.toInt32 >>> 8).toUInt32.toUInt8

/-- The digital modulation's symbol pitch: an octave below the carrier, raised by the first parameter. -/
@[inline] def modulationSymbolPitch (pitch param : Int16) : Int16 :=
  (pitch.toInt32 - (1536 : Int32) + ((param.toInt32 - 32767) >>> 3)).toInt16

/-- The digital modulation's symbol stream phase step. -/
@[inline] def modulationSymbolIncrement (pitch param : Int16) : UInt32 :=
  Pitch.phaseIncrement (modulationSymbolPitch pitch param)

/-- How far below note 128 a pitch is for the delay table, in pitch units, from 0 to 49152. Pitches at or
above note 128 are held at it. -/
@[inline] def delayBelow (pitch : Int16) : UInt32 :=
  let clamped := if pitch.toInt32 ≥ 16384 then 16384 else pitch.toInt32
  ((16384 : Int32) - clamped).toUInt32

/-- How many octaves down from the delay table a pitch is, from 0 to 32: the number of left shifts of its
delay beyond the table's 12. -/
@[inline] def delayShifts (pitch : Int16) : UInt32 := (delayBelow pitch + 1535) / 1536

/-- A pitch folded into the delay table's octave, from 0 to 1535. -/
@[inline] def delayFolded (pitch : Int16) : UInt32 := delayShifts pitch * 1536 - delayBelow pitch

/-- Which delay table entry a pitch falls on. The entry after it is blended in. -/
@[inline] def delayIndex (pitch : Int16) : UInt32 := delayFolded pitch >>> 4

/-- The delay-line length for a pitch, as a 16.16 fraction of samples: the table's top-octave length at the
folded pitch, the two nearest entries blended by the low four pitch bits, shifted down by 12 less one per
octave. More than 12 octaves down, the shift count wraps as the chip's shifter reads it. -/
@[inline] def delay (pitch : Int16) : UInt32 :=
  let a := delayTable (delayIndex pitch)
  let b := delayTable (delayIndex pitch + 1)
  let blended := a + (((b - a).toInt32 * (delayFolded pitch &&& 0xF).toInt32) >>> 4).toUInt32
  blended >>> (12 - delayShifts pitch)

end DigitalSetup
