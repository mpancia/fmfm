import Firmware.PercussionSetup

/-!
The block setup of the percussion engines hands the sample arithmetic (`Proofs/Percussion.lean`) its decays,
amplitudes, filter coefficient and gains. These theorems show the numbers it hands over are the ones the
sample theorems assume, so their hypotheses about "what the C++ sets" are met by construction.
-/

/-- An `Int32` shifted right one place is its value halved, rounded down. -/
private theorem percussion_setup_shift_one (s : Int32) : (s >>> 1).toInt = s.toInt / 2 := by
  show (s >>> 1).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by fourteen places. -/
private theorem percussion_setup_shift_fourteen (s : Int32) : (s >>> 14).toInt = s.toInt / 16384 := by
  show (s >>> 14).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- A 32-bit subtraction whose true difference fits is exact. -/
private theorem percussion_setup_sub_exact (a b : Int32) (fits : (a.toInt - b.toInt).natAbs < 2 ^ 31) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int32.toInt_sub]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A 32-bit addition whose true sum fits is exact. -/
private theorem percussion_setup_add_exact (a b : Int32) (fits : (a.toInt + b.toInt).natAbs < 2 ^ 31) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A 32-bit product whose true value fits is exact. -/
private theorem percussion_setup_mul_exact (a b : Int32) (fits : (a.toInt * b.toInt).natAbs < 2 ^ 31) :
    (a * b).toInt = a.toInt * b.toInt := by
  rw [Int32.toInt_mul]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A signed value between 0 and 32767 keeps its value as an unsigned one. -/
private theorem percussion_setup_small_toUInt32 (p : Int32) (lo : 0 ≤ p.toInt) (hi : p.toInt ≤ 32767) :
    p.toUInt32.toNat = p.toInt.toNat := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- Every bell and drum partial's two decays are 16-bit, the short one at most the long one; these are the
`decayFits` hypotheses of `percussion_decay_never_grows`.
Why it matters: a decay above 65535, or a short one above the long one, would make `Percussion.decay` a gain
and the partials would grow. -/
theorem percussion_setup_partial_decay_in_table (i : UInt32) :
    (0 ≤ (PercussionSetup.bellDecayShort i).toInt ∧
      (PercussionSetup.bellDecayShort i).toInt ≤ (PercussionSetup.bellDecayLong i).toInt ∧
      (PercussionSetup.bellDecayLong i).toInt ≤ 65535) ∧
    (0 ≤ (PercussionSetup.drumDecayShort i).toInt ∧
      (PercussionSetup.drumDecayShort i).toInt ≤ (PercussionSetup.drumDecayLong i).toInt ∧
      (PercussionSetup.drumDecayLong i).toInt ≤ 65535) := by
  unfold PercussionSetup.bellDecayShort PercussionSetup.bellDecayLong PercussionSetup.drumDecayShort
    PercussionSetup.drumDecayLong
  split <;> split <;> decide

/-- Every bell and drum partial starts within 16 bits, and the drum's second partial starts at or below 4096
and its fourth at or below 8192. The first is the `amplitudeFits` hypothesis of
`percussion_bell_partial_never_wraps` and `percussion_drum_partial_never_wraps`; the second, halved by the
sine, gives the 2048 and 4096 bounds `percussion_drum_mix_never_wraps` assumes.
Why it matters: the drum ring-modulates its second and fourth partials by the noise and then by a gain; a
louder start would pass 32 bits in the mix. -/
theorem percussion_setup_amplitudes_in_range (i : UInt32) :
    (0 ≤ (PercussionSetup.bellAmplitude i).toInt ∧ (PercussionSetup.bellAmplitude i).toInt ≤ 32767) ∧
    (0 ≤ (PercussionSetup.drumAmplitude i).toInt ∧ (PercussionSetup.drumAmplitude i).toInt ≤ 32767) ∧
    (PercussionSetup.drumAmplitude 1).toInt ≤ 4096 ∧ (PercussionSetup.drumAmplitude 3).toInt ≤ 8192 := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · unfold PercussionSetup.bellAmplitude; split <;> decide
  · unfold PercussionSetup.drumAmplitude; split <;> decide

/-- The drum's cutoff, after its clamp, is between 0 and 32767. -/
private theorem percussion_setup_drum_cutoff_clamped (pitch param1 : Int32) :
    0 ≤ (PercussionSetup.drumCutoff pitch param1).toInt ∧
      (PercussionSetup.drumCutoff pitch param1).toInt ≤ 32767 := by
  unfold PercussionSetup.drumCutoff
  dsimp only
  generalize pitch - (1536 : Int32) + param1 >>> 2 = cutoff
  split
  · simp
  · split
    · simp
    · rename_i a b
      simp only [gt_iff_lt] at b
      rw [Int32.lt_iff_toInt_lt] at a b
      have c0 : (0 : Int32).toInt = 0 := by decide
      have c32767 : (32767 : Int32).toInt = 32767 := by decide
      rw [c0] at a
      rw [c32767] at b
      omega

/-- The drum's noise filter reads its two cutoff entries inside the 257-entry cutoff table; the clamped
cutoff, shifted by 16, has a top byte of at most 127.
Why it matters: the drum's cutoff is the pitch plus a parameter, and the clamp keeps that sum's table read
inside the data. -/
theorem percussion_setup_drum_cutoff_in_table (pitch param1 : Int32) :
    (Analog.tableIndex ((PercussionSetup.drumCutoff pitch param1).toUInt32 <<< 16) + 1).toNat ≤ 128 := by
  have ⟨lo, hi⟩ := percussion_setup_drum_cutoff_clamped pitch param1
  have bound := percussion_setup_small_toUInt32 _ lo hi
  generalize (PercussionSetup.drumCutoff pitch param1).toUInt32 = c at bound
  have small : c.toNat ≤ 32767 := by omega
  unfold Analog.tableIndex
  have shifted : ((c <<< 16) >>> 24).toNat = c.toNat * 2 ^ 16 / 2 ^ 24 := by
    rw [UInt32.toNat_shiftRight, UInt32.toNat_shiftLeft]
    have h16 : (UInt32.toNat 16 % 32) = 16 := by decide
    have h24 : (UInt32.toNat 24 % 32) = 24 := by decide
    rw [h16, h24, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
  have lt : ((c <<< 16) >>> 24).toNat < 128 := by rw [shifted]; omega
  rw [UInt32.toNat_add]
  simp
  omega

/-- The gains handed to the drum and snare mixes are in the ranges their sample theorems assume: the drum's
noise gain 0 to 12888 and harmonics gain 0 to 16983 (`percussion_drum_mix_never_wraps`), the snare's two
gains 0 to 22000 and 0 to 38383 (`percussion_snare_never_wraps`), for parameters from 0 to 32767.
Why it matters: the mixes multiply a signal by these gains and add; a gain outside its range could push the
sum past 32 bits. -/
theorem percussion_setup_gains_in_range (param0 param1 : Int32)
    (param0Fits : 0 ≤ param0.toInt ∧ param0.toInt ≤ 32767)
    (param1Fits : 0 ≤ param1.toInt ∧ param1.toInt ≤ 32767) :
    (0 ≤ (PercussionSetup.drumNoiseGain param1).toInt ∧
      (PercussionSetup.drumNoiseGain param1).toInt ≤ 12888) ∧
    (0 ≤ (PercussionSetup.drumHarmonicsGain param1).toInt ∧
      (PercussionSetup.drumHarmonicsGain param1).toInt ≤ 16983) ∧
    (0 ≤ (PercussionSetup.snareGain1 param0).toInt ∧ (PercussionSetup.snareGain1 param0).toInt ≤ 22000) ∧
    (0 ≤ (PercussionSetup.snareGain2 param0).toInt ∧ (PercussionSetup.snareGain2 param0).toInt ≤ 38383) := by
  have half : (param0 >>> 1).toInt = param0.toInt / 2 := percussion_setup_shift_one param0
  have c22000 : (22000 : Int32).toInt = 22000 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold PercussionSetup.drumNoiseGain
    generalize h : (if param1 < 16384 then (0 : Int32) else param1 - 16384) = raw
    have rawFits : 0 ≤ raw.toInt ∧ raw.toInt ≤ 16383 := by
      subst h
      split
      · simp
      · rename_i a
        rw [Int32.lt_iff_toInt_lt] at a
        have c16384 : (16384 : Int32).toInt = 16384 := by decide
        rw [percussion_setup_sub_exact _ _ (by rw [c16384]; omega), c16384]
        rw [c16384] at a
        omega
    have c12888 : (12888 : Int32).toInt = 12888 := by decide
    rw [percussion_setup_shift_fourteen, percussion_setup_mul_exact _ _ (by rw [c12888]; omega), c12888]
    omega
  · unfold PercussionSetup.drumHarmonicsGain
    split
    · rename_i a
      rw [Int32.lt_iff_toInt_lt] at a
      have c12888 : (12888 : Int32).toInt = 12888 := by decide
      have c4096 : (4096 : Int32).toInt = 4096 := by decide
      rw [c12888] at a
      rw [percussion_setup_add_exact _ _ (by rw [c4096]; omega), c4096]
      omega
    · decide
  · unfold PercussionSetup.snareGain1
    rw [percussion_setup_sub_exact _ _ (by rw [c22000, half]; omega), c22000, half]
    omega
  · unfold PercussionSetup.snareGain2
    rw [percussion_setup_add_exact _ _ (by rw [c22000, half]; omega), c22000, half]
    omega
