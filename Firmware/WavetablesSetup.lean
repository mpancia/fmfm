import Firmware.Wavetables
import Firmware.Pitch
import Firmware.BraidsData

set_option compiler.extract_closed false

/-!
# Wavetable engines, the setup of one block

Port of what `DigitalOscillator::RenderWavetables`, `RenderWaveMap`, `RenderWaveLine` and
`RenderWaveParaphonic` compute before their loops (Braids, Emilie Gillet, MIT): which waves a block plays,
the crossfades between them and the paraphonic voices' phase steps, from the pitch and the two parameters.
The loops are in `Firmware/Wavetables.lean`. Lean shifts bind tighter than `*` and `+`, so shifted products
are parenthesized.
-/

namespace WavetablesSetup

/-- How many steps one of Braids' 20 wavetables has (`wavetable_definitions` in `digital_oscillator.cc`).
The body is the data, generated from the C source (`BraidsData.wavetableSteps`); on the chip the C reads its
own copy. Trusted: that the one-line C accessor reads the same table. -/
@[extern "fm1_braids_wavetable_steps"] def tableSteps (table : UInt32) : UInt32 :=
  (BraidsData.wavetableSteps table.toNat).toUInt32

/-- The wave at a step of one of Braids' 20 wavetables (17 steps each), looked up by C. Trusted data. -/
@[extern "fm1_braids_wavetable_wave"] opaque tableWave (table step : UInt32) : UInt32

/-- One entry of Braids' 16 by 16 wave map (`wt_map`, 256 entries), looked up by C. Trusted data. -/
@[extern "fm1_braids_wt_map"] opaque mapTable (index : UInt32) : UInt8

/-- One entry of Braids' wave line (64 waves), looked up by C. Trusted data. -/
@[extern "fm1_braids_wave_line"] opaque lineTable (index : UInt32) : UInt8

/-- One entry of Braids' short wave line (33 waves), looked up by C. Trusted data. -/
@[extern "fm1_braids_mini_wave_line"] opaque miniLineTable (index : UInt32) : UInt8

/-- One voice's detune of one of Braids' 17 chords, in pitch units, looked up by C. Trusted data. -/
@[extern "fm1_braids_chord"] opaque chordTable (chord voice : UInt32) : UInt32

/-- Wavetables: which of the 20 wavetables the held second parameter selects. -/
@[inline] def tableIndex (prev1 : Int16) : UInt32 := (prev1.toInt32.toUInt32 * 20) >>> 15

/-- Wavetables: where in the table the first parameter points, in steps with a 16-bit fraction. -/
@[inline] def wavePointer (param0 prev1 : Int16) : UInt32 :=
  ((param0.toInt32 * 2) * (tableSteps (tableIndex prev1)).toInt32).toUInt32

/-- Wavetables: the step the pointer is on. -/
@[inline] def tableStep (param0 prev1 : Int16) : UInt32 := wavePointer param0 prev1 >>> 16

/-- Wavetables: the wave at the pointer's step, or the one after it. -/
@[inline] def tableWaveAt (param0 prev1 : Int16) (next : UInt32) : UInt32 :=
  tableWave (tableIndex prev1) (tableStep param0 prev1 + next)

/-- Wavetables: the crossfade between the two waves, 16 bits. -/
@[inline] def tableBalance (param0 prev1 : Int16) : UInt32 := wavePointer param0 prev1 &&& 0xFFFF

/-- Wave map: a parameter scaled to the 15 squares of the 16 by 16 grid, as a 16-bit value. -/
@[inline] def mapPosition (param : Int16) : UInt16 := ((param.toInt32 * 15) >>> 4).toUInt32.toUInt16

/-- Wave map: the crossfade within a square along one axis, 16 bits. -/
@[inline] def mapXfade (param : Int16) : UInt32 := ((mapPosition param).toUInt32 <<< 5).toUInt16.toUInt32

/-- Wave map: the square's row or column, 0 to 14. -/
@[inline] def mapCoordinate (param : Int16) : UInt32 := (mapPosition param).toUInt32 >>> 11

/-- Wave map: where a corner of the square lies in the map, `i` and `j` 0 or 1. -/
@[inline] def mapIndex (param0 param1 : Int16) (i j : UInt32) : UInt32 :=
  ((mapCoordinate param0 + i) * 16 + (mapCoordinate param1 + j)) &&& 0xFFFF

/-- Wave map: the wave at a corner of the square. -/
@[inline] def mapWave (param0 param1 : Int16) (i j : UInt32) : UInt32 :=
  (mapTable (mapIndex param0 param1 i j)).toUInt32

/-- Wave line: the first parameter, doubled, smoothed by a quarter per block. -/
@[inline] def smoothed (previous : Int32) (param0 : Int16) : Int32 :=
  ((3 : Int32) * previous + param0.toInt32 * 2) >>> 2

/-- Wave line: where the smoothed parameter scans the line, 16 bits. -/
@[inline] def lineScan (previous : Int32) (param0 : Int16) : UInt16 :=
  (smoothed previous param0).toUInt32.toUInt16

/-- Wave line: the wave the held first parameter points at. -/
@[inline] def lineWave0 (prev0 : Int16) : UInt32 := (lineTable (prev0.toInt32 >>> 9).toUInt32).toUInt32

/-- Wave line: the wave the scan points at, or the one after it. -/
@[inline] def lineWaveAt (previous : Int32) (param0 : Int16) (next : UInt32) : UInt32 :=
  (lineTable (((lineScan previous param0).toUInt32 >>> 10) + next)).toUInt32

/-- Wave line: the crossfade between the scan's two waves, 16 bits. -/
@[inline] def lineSmoothXfade (previous : Int32) (param0 : Int16) : UInt32 :=
  ((lineScan previous param0).toUInt32 <<< 6).toUInt16.toUInt32

/-- Wave line: how far the rough crossfade moves per sample over a block of `size` samples. -/
@[inline] def lineRoughStep (size : UInt32) : UInt32 := 32768 / size

/-- Wave line: the balance between the smooth and the rough reading, from the second parameter. -/
@[inline] def lineBalance (param1 : Int16) : UInt32 := (param1.toInt32 <<< 3).toUInt32

/-- Wave line: which quarter of the second parameter's range selects the reading mode, 0 to 3. -/
@[inline] def lineMode (param1 : Int16) : UInt32 :=
  if param1.toInt32 < 8192 then 0 else if param1.toInt32 < 16384 then 1
  else if param1.toInt32 < 24576 then 2 else 3

/-- Wave line: the held first parameter after the block, the smoothed value halved. -/
@[inline] def lineHeld (previous : Int32) (param0 : Int16) : Int16 :=
  ((smoothed previous param0) >>> 1).toInt16

/-- Paraphonic: which of the 17 chords the second parameter is on. -/
@[inline] def chordIndex (param1 : Int16) : UInt32 := (param1.toInt32 >>> 11).toUInt32

/-- Paraphonic: the blend towards the next chord, 16 bits, held at either chord outside a narrow band. -/
@[inline] def chordFraction (param1 : Int16) : UInt32 :=
  let fractional := (param1.toInt32 <<< 5).toUInt32.toUInt16.toUInt32
  if fractional < 30720 then 0 else if fractional ≥ 34816 then 65535 else (fractional - 30720) * 16

/-- Paraphonic: one voice's detune, the two chords' blended, cut to 16 bits as Braids does. -/
@[inline] def chordDetune (param1 : Int16) (voice : UInt32) : UInt32 :=
  let a := (chordTable (chordIndex param1) voice).toInt32
  let b := (chordTable (chordIndex param1 + 1) voice).toInt32
  (a + (((b - a) * (chordFraction param1).toInt32) >>> 16)).toUInt32.toUInt16.toUInt32

/-- Paraphonic: one of the three detuned voices' phase steps. -/
@[inline] def voiceIncrement (pitch param1 : Int16) (voice : UInt32) : UInt32 :=
  Pitch.phaseIncrement (pitch.toInt32 + (chordDetune param1 voice).toInt32).toInt16

/-- Paraphonic: the wave the first parameter points at in the short line, or the one after it. -/
@[inline] def miniLineWaveAt (param0 : Int16) (next : UInt32) : UInt32 :=
  (miniLineTable ((param0.toInt32 >>> 10).toUInt32 + next)).toUInt32

/-- Paraphonic: the crossfade between the two waves, 16 bits. -/
@[inline] def miniLineXfade (param0 : Int16) : UInt32 := (param0.toInt32 <<< 6).toUInt32.toUInt16.toUInt32

end WavetablesSetup
