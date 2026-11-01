import Firmware.WavetablesSetup

set_option compiler.extract_closed false

/-! C entry points for `Firmware/WavetablesSetup.lean`: one function per value a block's setup hands to the
loop. -/

/-- `wavetables`: the wave at the pointer's step (`next` 0) or the one after it (`next` 1). -/
@[export fm1_wavetables_setup_table_wave] def wavetablesSetupTableWave (param0 : Int16) (prev1 : Int16)
    (next : UInt32) : UInt32 :=
  WavetablesSetup.tableWaveAt param0 prev1 next

/-- `wavetables`: the crossfade between the two waves. -/
@[export fm1_wavetables_setup_table_balance] def wavetablesSetupTableBalance (param0 : Int16)
    (prev1 : Int16) : UInt32 :=
  WavetablesSetup.tableBalance param0 prev1

/-- `wave_map`: the wave at corner `i`, `j` of the square. -/
@[export fm1_wavetables_setup_map_wave] def wavetablesSetupMapWave (param0 : Int16) (param1 : Int16)
    (i : UInt32) (j : UInt32) : UInt32 :=
  WavetablesSetup.mapWave param0 param1 i j

/-- `wave_map`: the crossfade along one axis. -/
@[export fm1_wavetables_setup_map_xfade] def wavetablesSetupMapXfade (param : Int16) : UInt32 :=
  WavetablesSetup.mapXfade param

/-- `wave_line`: the smoothed first parameter. -/
@[export fm1_wavetables_setup_line_smoothed] def wavetablesSetupLineSmoothed (previous : Int32)
    (param0 : Int16) : Int32 :=
  WavetablesSetup.smoothed previous param0

/-- `wave_line`: the wave the held first parameter points at. -/
@[export fm1_wavetables_setup_line_wave0] def wavetablesSetupLineWave0 (prev0 : Int16) : UInt32 :=
  WavetablesSetup.lineWave0 prev0

/-- `wave_line`: the wave the scan points at (`next` 0) or the one after it (`next` 1). -/
@[export fm1_wavetables_setup_line_wave] def wavetablesSetupLineWave (previous : Int32) (param0 : Int16)
    (next : UInt32) : UInt32 :=
  WavetablesSetup.lineWaveAt previous param0 next

/-- `wave_line`: the smooth crossfade. -/
@[export fm1_wavetables_setup_line_smooth_xfade] def wavetablesSetupLineSmoothXfade (previous : Int32)
    (param0 : Int16) : UInt32 :=
  WavetablesSetup.lineSmoothXfade previous param0

/-- `wave_line`: the rough crossfade's step per sample. -/
@[export fm1_wavetables_setup_line_rough_step] def wavetablesSetupLineRoughStep (size : UInt32) : UInt32 :=
  WavetablesSetup.lineRoughStep size

/-- `wave_line`: the balance between the readings. -/
@[export fm1_wavetables_setup_line_balance] def wavetablesSetupLineBalance (param1 : Int16) : UInt32 :=
  WavetablesSetup.lineBalance param1

/-- `wave_line`: the reading mode. -/
@[export fm1_wavetables_setup_line_mode] def wavetablesSetupLineMode (param1 : Int16) : UInt32 :=
  WavetablesSetup.lineMode param1

/-- `wave_line`: the held first parameter after the block. -/
@[export fm1_wavetables_setup_line_held] def wavetablesSetupLineHeld (previous : Int32) (param0 : Int16) :
    Int16 :=
  WavetablesSetup.lineHeld previous param0

/-- `wave_paraphonic`: a detuned voice's phase step, `voice` 0 to 2. -/
@[export fm1_wavetables_setup_voice_increment] def wavetablesSetupVoiceIncrement (pitch : Int16)
    (param1 : Int16) (voice : UInt32) : UInt32 :=
  WavetablesSetup.voiceIncrement pitch param1 voice

/-- `wave_paraphonic`: the wave the first parameter points at (`next` 0) or the one after it (`next` 1). -/
@[export fm1_wavetables_setup_mini_line_wave] def wavetablesSetupMiniLineWave (param0 : Int16)
    (next : UInt32) : UInt32 :=
  WavetablesSetup.miniLineWaveAt param0 next

/-- `wave_paraphonic`: the crossfade between the two waves. -/
@[export fm1_wavetables_setup_mini_line_xfade] def wavetablesSetupMiniLineXfade (param0 : Int16) : UInt32 :=
  WavetablesSetup.miniLineXfade param0
