import Firmware.VoiceSetup
import Firmware.Pitch

/-!
The voice narrows what the firmware sends to the 16 bits Braids holds. These theorems say nothing is lost for
what the firmware can send: a MIDI note times 128, timbre values of 0 to 32767, and a shape index.
-/

/-- A value between -32768 and 32767 survives the cut to 16 bits. -/
private theorem voice_setup_keep16 (x : Int32) (lo : -32768 ≤ x.toInt) (hi : x.toInt ≤ 32767) :
    x.toInt16.toInt = x.toInt := by
  rw [Int32.toInt_toInt16]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A note of at most 127 times 128 keeps its value as a signed 32-bit number. -/
private theorem voice_setup_note_times (note : UInt32) (midi : note.toNat ≤ 127) :
    (note.toInt32 * 128).toInt = note.toNat * 128 := by
  have small : note.toInt32.toInt = note.toNat := by
    show note.toBitVec.toInt = _
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]
    rfl
  rw [Int32.toInt_mul, small]
  exact Int.bmod_eq_of_le (by simp; omega) (by simp; omega)

/-- The pitch Braids gets for a MIDI note (`play` in `fw/firmware/src/dinghy.c` sends the note times 128) is
exactly that below note 128, where the phase step clamps, and a timbre value of 0 to 32767 (the sounds' range,
and what the envelope's boost is held to) reaches Braids unchanged.
Why it matters: Braids holds pitch and timbre in 16 bits; the firmware's range never reaches the cut, so no
note plays the wrong pitch and no parameter reads past the tables. -/
theorem voice_setup_pitch_in_range (note : UInt32) (midi : note.toNat ≤ 127) (timbre : Int32)
    (lo : 0 ≤ timbre.toInt) (hi : timbre.toInt ≤ 32767) :
    (VoiceSetup.pitch (note.toInt32 * 128)).toInt = note.toNat * 128 ∧
      (VoiceSetup.pitch (note.toInt32 * 128)).toInt32 < Pitch.tableStart ∧
      (VoiceSetup.parameter timbre).toInt = timbre.toInt := by
  have times := voice_setup_note_times note midi
  have kept : (VoiceSetup.pitch (note.toInt32 * 128)).toInt = note.toNat * 128 := by
    unfold VoiceSetup.pitch
    rw [voice_setup_keep16 _ (by omega) (by omega), times]
  refine ⟨kept, ?_, ?_⟩
  · rw [Int32.lt_iff_toInt_lt, Int16.toInt_toInt32, kept]
    have start : Pitch.tableStart.toInt = 16384 := by decide
    omega
  · unfold VoiceSetup.parameter
    exact voice_setup_keep16 _ (by omega) (by omega)

/-- The shape the voice plays is one of Braids' 48, whatever index the firmware sends.
Why it matters: the macro oscillator picks its render function from a 48-entry table without a check. -/
theorem voice_setup_shape_in_table (shape : UInt32) : (VoiceSetup.shape shape).toNat < 48 := by
  unfold VoiceSetup.shape
  split
  · decide
  · rename_i below
    rw [UInt32.not_le, UInt32.lt_iff_toNat_lt] at below
    exact below
