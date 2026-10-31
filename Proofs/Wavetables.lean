import Firmware.Wavetables
import Proofs.Blend

/-- An `Int32` shifted right one place is its value halved, rounded down. -/
private theorem wavetables_shift_one (s : Int32) : (s >>> 1).toInt = s.toInt / 2 := by
  have : (s >>> 1).toInt = s.toInt >>> 1 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (1 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- A crossfade of two waves is a 16-bit value. -/
private theorem wavetables_crossfade_range (waveA waveB phase balance : UInt32) :
    -32768 ≤ (Wavetables.crossfade waveA waveB phase balance).toInt ∧
      (Wavetables.crossfade waveA waveB phase balance).toInt ≤ 32767 := by
  unfold Wavetables.crossfade
  dsimp only
  rw [Int16.toInt_toInt32, Int32.toInt_toInt16]
  simp [Int.bmod_def]
  split <;> omega

/-- A wavetable sample is exactly the sum of its two half-rate readings, each halved: nothing wraps around.
Why it matters: the wavetable engine cannot click from an overflow, for any waves, phase or morph position. -/
theorem wavetables_wavetable_never_wraps (phase inc waveA waveB balance : UInt32) (sync : UInt8) :
    (Wavetables.wavetable phase inc waveA waveB balance sync).out.toInt =
      (Wavetables.crossfade waveA waveB ((if sync != 0 then 0 else phase + inc) >>> 1) balance).toInt / 2 +
      (Wavetables.crossfade waveA waveB (((if sync != 0 then 0 else phase + inc) + inc) >>> 1)
        balance).toInt / 2 := by
  unfold Wavetables.wavetable
  dsimp only
  generalize hs : (if sync != 0 then 0 else phase + inc) = start
  have h1 := wavetables_crossfade_range waveA waveB (start >>> 1) balance
  have h2 := wavetables_crossfade_range waveA waveB ((start + inc) >>> 1) balance
  generalize Wavetables.crossfade waveA waveB (start >>> 1) balance = a at *
  generalize Wavetables.crossfade waveA waveB ((start + inc) >>> 1) balance = b at *
  rw [Int32.toInt_toInt16, Int32.toInt_add, wavetables_shift_one, wavetables_shift_one]
  simp [Int.bmod_def]
  split <;> omega

/-- A crossfade of two waves at the same phase lies between the two waves' values there, as long as they
are at most 32767 apart.
Why it matters: morphing between waves can never be louder than the louder wave, at any morph position. -/
theorem wavetables_crossfade_between_waves (waveA waveB phase balance : UInt32)
    (near : -32767 ≤ (Wavetables.read waveB phase).toInt - (Wavetables.read waveA phase).toInt ∧
      (Wavetables.read waveB phase).toInt - (Wavetables.read waveA phase).toInt ≤ 32767) :
    min (Wavetables.read waveA phase).toInt (Wavetables.read waveB phase).toInt ≤
        (Wavetables.crossfade waveA waveB phase balance).toInt ∧
      (Wavetables.crossfade waveA waveB phase balance).toInt ≤
        max (Wavetables.read waveA phase).toInt (Wavetables.read waveB phase).toInt := by
  have ra : -32768 ≤ (Wavetables.read waveA phase).toInt ∧ (Wavetables.read waveA phase).toInt ≤ 32767 := by
    unfold Wavetables.read; dsimp only
    rw [Int16.toInt_toInt32, Int32.toInt_toInt16]; simp [Int.bmod_def]; split <;> omega
  have rb : -32768 ≤ (Wavetables.read waveB phase).toInt ∧ (Wavetables.read waveB phase).toInt ≤ 32767 := by
    unfold Wavetables.read; dsimp only
    rw [Int16.toInt_toInt32, Int32.toInt_toInt16]; simp [Int.bmod_def]; split <;> omega
  unfold Wavetables.crossfade
  dsimp only
  exact blend_sixteen_between _ _ balance ra rb near
