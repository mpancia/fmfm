import Firmware.Punch

set_option compiler.extract_closed false

/-! C entry points for `Firmware/Punch.lean`: `fw/firmware/src/dinghy.c` calls them each tick (tempo,
re-strikes,
transposition, mutes, the effect amounts, the gate's target) and `voices/punch_glue.c` each sample (the
gate and
the crush). All plain 32-bit numbers; `Punch.held`'s key number is small. -/

/-- The clock's speed in percent. -/
@[export fm1_punch_tempo] def punchTempo (keys : UInt32) : UInt32 := Punch.tempoPercent keys
/-- 1 if this tick re-strikes every sounding note. -/
@[export fm1_punch_restrike] def punchRestrike (keys choice tick : UInt32) : UInt32 :=
  if Punch.restrike keys choice tick then 1 else 0
/-- A note transposed and held to the MIDI range. -/
@[export fm1_punch_note] def punchNote (keys shift note : UInt32) : UInt32 := Punch.note keys shift note
/-- The gate's target gain on this tick, Q15. -/
@[export fm1_punch_gate_target] def punchGateTarget (keys choice tick : UInt32) : UInt32 :=
  Punch.gateTarget (Punch.gateOpen keys choice tick)
/-- The gate's gain one sample on. -/
@[export fm1_punch_gate_step] def punchGateStep (gain target : UInt32) : UInt32 := Punch.gateStep gain target
/-- A mix sample through the gate. -/
@[export fm1_punch_gate_sample] def punchGateSample (sample : Int32) (gain : UInt32) : Int32 :=
  Punch.gateSample sample gain
/-- The crush's hold, in samples. -/
@[export fm1_punch_crush_factor] def punchCrushFactor (keys factor : UInt32) : UInt32 := Punch.crushFactor
    keys factor
/-- A mix sample through the crush. -/
@[export fm1_punch_crush_sample] def punchCrushSample (factor index : UInt32) (heldSample sample : Int32) :
    Int32 :=
  Punch.crushSample factor index heldSample sample
/-- The reverb amount with the keys. -/
@[export fm1_punch_reverb_amount] def punchReverbAmount (keys base : UInt32) : UInt32 := Punch.reverbAmount
    keys base
/-- The delay amount with the keys. -/
@[export fm1_punch_delay_amount] def punchDelayAmount (keys base : UInt32) : UInt32 := Punch.delayAmount
    keys base
/-- 1 if lane `lane` is muted by a key. -/
@[export fm1_punch_lane_muted] def punchLaneMuted (keys lane : UInt32) : UInt32 :=
  if Punch.laneMuted keys lane then 1 else 0
