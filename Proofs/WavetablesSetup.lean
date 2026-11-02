import Firmware.WavetablesSetup
import Proofs.Pitch
import Proofs.Tables
import Proofs.BraidsData

/-!
The wavetable engines' setup picks waves out of small C tables (a wavetable's steps, the wave map, the two
wave lines, the chords) and names them by their number in the 33024-byte bank of 129-byte waves. These
theorems say the picks stay inside those tables and a picked wave's bytes stay inside the bank, for the
parameters Braids' voice sends (0 to 32767).
-/

/-- A 16-bit parameter's value as a 32-bit number is the same number. -/
private theorem wavetables_setup_param (p : Int16) : p.toInt32.toInt = p.toInt := Int16.toInt_toInt32 p

/-- An `Int32` shifted right `k` places is its value divided by `2^k`, rounded down: the cases used here. -/
private theorem wavetables_setup_shift_two (s : Int32) : (s >>> 2).toInt = s.toInt / 4 := by
  show (s >>> 2).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by four places. -/
private theorem wavetables_setup_shift_four (s : Int32) : (s >>> 4).toInt = s.toInt / 16 := by
  show (s >>> 4).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by nine places. -/
private theorem wavetables_setup_shift_nine (s : Int32) : (s >>> 9).toInt = s.toInt / 512 := by
  show (s >>> 9).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by ten places. -/
private theorem wavetables_setup_shift_ten (s : Int32) : (s >>> 10).toInt = s.toInt / 1024 := by
  show (s >>> 10).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by eleven places. -/
private theorem wavetables_setup_shift_eleven (s : Int32) : (s >>> 11).toInt = s.toInt / 2048 := by
  show (s >>> 11).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by one place. -/
private theorem wavetables_setup_shift_one (s : Int32) : (s >>> 1).toInt = s.toInt / 2 := by
  show (s >>> 1).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- A signed value that is not negative keeps its value as an unsigned one. -/
private theorem wavetables_setup_toUInt32_of_nonneg (p : Int32) (nonneg : 0 ≤ p.toInt) :
    (p.toUInt32.toNat : Int) = p.toInt := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- A `UInt32` below 2^31 keeps its value as an `Int32`. -/
private theorem wavetables_setup_small_toInt32 (x : UInt32) (below : x.toNat < 2 ^ 31) :
    x.toInt32.toInt = (x.toNat : Int) := by
  show x.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · simp
  · simp at below ⊢; omega

/-- A `UInt32` shifted right `k` places is its value divided by `2^k`. -/
private theorem wavetables_setup_ushift (x k : UInt32) (small : k.toNat < 32) :
    (x >>> k).toNat = x.toNat / 2 ^ k.toNat := by
  rw [UInt32.toNat_shiftRight, Nat.mod_eq_of_lt small, Nat.shiftRight_eq_div_pow]

/-- Adding one to an index that is not at the top of the 32-bit range adds one to its value. -/
private theorem wavetables_setup_succ (x : UInt32) (small : x.toNat < 4294967295) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt32.toNat_add]
  simp
  omega

/-- The wavetable's index is at most 19 for a held parameter from 0 to 32767. -/
private theorem wavetables_setup_table_index_le (prev1 : Int16) (nonneg : 0 ≤ prev1.toInt) :
    (WavetablesSetup.tableIndex prev1).toNat ≤ 19 := by
  have hi := Int16.toInt_le prev1
  have top : Int16.maxValue.toInt = 32767 := by decide
  have value := wavetables_setup_toUInt32_of_nonneg prev1.toInt32 (by rw [wavetables_setup_param]; omega)
  rw [wavetables_setup_param] at value
  unfold WavetablesSetup.tableIndex
  rw [wavetables_setup_ushift _ _ (by decide), UInt32.toNat_mul, Nat.mod_eq_of_lt (by simp; omega)]
  simp
  omega

/-- The wave pointer is at most 2 * 32767 * 16 for a parameter from 0 to 32767 (every table has at most 16
steps). -/
private theorem wavetables_setup_pointer_le (param0 prev1 : Int16) (nonneg : 0 ≤ param0.toInt) :
    (WavetablesSetup.wavePointer param0 prev1).toNat ≤ 1048544 := by
  have steps := braids_data_wavetable_steps_at_most_16 (WavetablesSetup.tableIndex prev1)
  have hi := Int16.toInt_le param0
  have top : Int16.maxValue.toInt = 32767 := by decide
  have p := wavetables_setup_param param0
  have doubled : (param0.toInt32 * 2).toInt = param0.toInt * 2 := by
    rw [Int32.toInt_mul, p]; exact Int.bmod_eq_of_le (by simp; omega) (by simp; omega)
  generalize n : (WavetablesSetup.tableSteps (WavetablesSetup.tableIndex prev1)) = count at steps ⊢
  have s := wavetables_setup_small_toInt32 count (by omega)
  have lo : 0 ≤ param0.toInt * 2 * count.toNat := Int.mul_nonneg (by omega) (by omega)
  have hi' : param0.toInt * 2 * count.toNat ≤ 65534 * 16 :=
    Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
  have product : ((param0.toInt32 * 2) * count.toInt32).toInt = param0.toInt * 2 * count.toNat := by
    rw [Int32.toInt_mul, doubled, s]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  unfold WavetablesSetup.wavePointer
  rw [n]
  have := wavetables_setup_toUInt32_of_nonneg _ (by rw [product]; exact lo)
  rw [product] at this
  omega

/-- The wavetable engine reads its wavetable's definition inside the table of 20 definitions, and the
pointer's step and the one after it inside the 17 steps of a definition, for a held parameter from 0 to 32767.
Every definition in `digital_oscillator.cc` has 4, 8 or 16 steps (`braids_data_wavetable_steps_at_most_16`).
Why it matters: both are C arrays read without a check; the 17th entry of each definition is there for the
read past the last step. -/
theorem wavetables_setup_table_in_table (param0 prev1 : Int16) (nonneg0 : 0 ≤ param0.toInt)
    (nonneg1 : 0 ≤ prev1.toInt) :
    (WavetablesSetup.tableIndex prev1).toNat ≤ 19 ∧
      (WavetablesSetup.tableStep param0 prev1 + 1).toNat ≤ 16 := by
  refine ⟨wavetables_setup_table_index_le prev1 nonneg1, ?_⟩
  have := wavetables_setup_pointer_le param0 prev1 nonneg0
  unfold WavetablesSetup.tableStep
  rw [wavetables_setup_succ _ (by rw [wavetables_setup_ushift _ _ (by decide)]; simp; omega),
    wavetables_setup_ushift _ _ (by decide)]
  simp
  omega

/-- A parameter from 0 to 32767 lands on a map position from 0 to 30719. -/
private theorem wavetables_setup_position_le (param : Int16) (nonneg : 0 ≤ param.toInt) :
    (WavetablesSetup.mapPosition param).toNat ≤ 30719 := by
  have hi := Int16.toInt_le param
  have top : Int16.maxValue.toInt = 32767 := by decide
  have scaled : (param.toInt32 * 15).toInt = param.toInt * 15 := by
    rw [Int32.toInt_mul, wavetables_setup_param]; exact Int.bmod_eq_of_le (by simp; omega) (by simp; omega)
  have shifted := wavetables_setup_shift_four (param.toInt32 * 15)
  rw [scaled] at shifted
  have := wavetables_setup_toUInt32_of_nonneg ((param.toInt32 * 15) >>> 4) (by rw [shifted]; omega)
  unfold WavetablesSetup.mapPosition
  rw [UInt32.toNat_toUInt16, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A map coordinate is from 0 to 14. -/
private theorem wavetables_setup_coordinate_le (param : Int16) (nonneg : 0 ≤ param.toInt) :
    (WavetablesSetup.mapCoordinate param).toNat ≤ 14 := by
  have := wavetables_setup_position_le param nonneg
  unfold WavetablesSetup.mapCoordinate
  have e : (2 : Nat) ^ (11 : UInt32).toNat = 2048 := by decide
  rw [wavetables_setup_ushift _ _ (by decide), UInt16.toNat_toUInt32, e]
  omega

/-- The wave map reads its four corners inside the 256-entry map for parameters from 0 to 32767 and corners
0 or 1 away from the square's origin.
Why it matters: the map is a C array read without a check; the scaling to 15 squares keeps the corner after
the last column or row inside the 16 by 16 grid. -/
theorem wavetables_setup_map_in_table (param0 param1 : Int16) (i j : UInt32) (nonneg0 : 0 ≤ param0.toInt)
    (nonneg1 : 0 ≤ param1.toInt) (cornerI : i.toNat ≤ 1) (cornerJ : j.toNat ≤ 1) :
    (WavetablesSetup.mapIndex param0 param1 i j).toNat ≤ 255 := by
  have c0 := wavetables_setup_coordinate_le param0 nonneg0
  have c1 := wavetables_setup_coordinate_le param1 nonneg1
  unfold WavetablesSetup.mapIndex
  rw [UInt32.toNat_and]
  have inner : ((WavetablesSetup.mapCoordinate param0 + i) * 16 +
      (WavetablesSetup.mapCoordinate param1 + j)).toNat ≤ 255 := by
    rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_add, UInt32.toNat_add]
    simp
    omega
  have := Nat.and_le_left (n := ((WavetablesSetup.mapCoordinate param0 + i) * 16 +
    (WavetablesSetup.mapCoordinate param1 + j)).toNat) (m := (0xFFFF : UInt32).toNat)
  omega

/-- The smoothed parameter stays from 0 to 65534 for a parameter from 0 to 32767. -/
private theorem wavetables_setup_smoothed_range (previous : Int32) (param0 : Int16)
    (settled : 0 ≤ previous.toInt ∧ previous.toInt ≤ 65534) (nonneg : 0 ≤ param0.toInt) :
    0 ≤ (WavetablesSetup.smoothed previous param0).toInt ∧
      (WavetablesSetup.smoothed previous param0).toInt ≤ 65534 := by
  have hi := Int16.toInt_le param0
  have top : Int16.maxValue.toInt = 32767 := by decide
  have tripled : ((3 : Int32) * previous).toInt = 3 * previous.toInt := by
    rw [Int32.toInt_mul]; exact Int.bmod_eq_of_le (by simp; omega) (by simp; omega)
  have doubled : (param0.toInt32 * 2).toInt = param0.toInt * 2 := by
    rw [Int32.toInt_mul, wavetables_setup_param]; exact Int.bmod_eq_of_le (by simp; omega) (by simp; omega)
  have sum : ((3 : Int32) * previous + param0.toInt32 * 2).toInt = 3 * previous.toInt + param0.toInt * 2 := by
    rw [Int32.toInt_add, tripled, doubled]; exact Int.bmod_eq_of_le (by omega) (by omega)
  unfold WavetablesSetup.smoothed
  rw [wavetables_setup_shift_two, sum]
  omega

/-- The scan is the smoothed parameter, from 0 to 65534. -/
private theorem wavetables_setup_scan_le (previous : Int32) (param0 : Int16)
    (settled : 0 ≤ previous.toInt ∧ previous.toInt ≤ 65534) (nonneg : 0 ≤ param0.toInt) :
    (WavetablesSetup.lineScan previous param0).toNat ≤ 65534 := by
  have ⟨lo, hi⟩ := wavetables_setup_smoothed_range previous param0 settled nonneg
  have := wavetables_setup_toUInt32_of_nonneg _ lo
  unfold WavetablesSetup.lineScan
  rw [UInt32.toNat_toUInt16, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The wave line reads the held parameter's wave and the scan's wave inside its 64-entry line, and the wave
after the scan's at most one past it, for parameters from 0 to 32767 and a smoothed parameter from 0 to
65534; both parameters stay in those ranges for the next block. The read one past the line is Braids' own:
at the top of the parameter's range the scan reaches the last wave and asks for the one after it. The port
keeps that read so the output matches Braids.
Why it matters: the line is a C array read without a check; the ranges are the invariant that bounds every
block's reads, starting from 0. -/
theorem wavetables_setup_line_in_table (previous : Int32) (prev0 param0 : Int16)
    (settled : 0 ≤ previous.toInt ∧ previous.toInt ≤ 65534) (held : 0 ≤ prev0.toInt)
    (nonneg : 0 ≤ param0.toInt) :
    (prev0.toInt32 >>> 9).toUInt32.toNat ≤ 63 ∧
      ((WavetablesSetup.lineScan previous param0).toUInt32 >>> 10).toNat ≤ 63 ∧
      ((WavetablesSetup.lineScan previous param0).toUInt32 >>> 10 + 1).toNat ≤ 64 ∧
      (0 ≤ (WavetablesSetup.smoothed previous param0).toInt ∧
        (WavetablesSetup.smoothed previous param0).toInt ≤ 65534) ∧
      0 ≤ (WavetablesSetup.lineHeld previous param0).toInt := by
  have hi := Int16.toInt_le prev0
  have top : Int16.maxValue.toInt = 32767 := by decide
  have shifted := wavetables_setup_shift_nine prev0.toInt32
  rw [wavetables_setup_param] at shifted
  have wave0 := wavetables_setup_toUInt32_of_nonneg (prev0.toInt32 >>> 9) (by rw [shifted]; omega)
  have scan := wavetables_setup_scan_le previous param0 settled nonneg
  have range := wavetables_setup_smoothed_range previous param0 settled nonneg
  have shiftedScan : ((WavetablesSetup.lineScan previous param0).toUInt32 >>> 10).toNat =
      (WavetablesSetup.lineScan previous param0).toNat / 1024 := by
    have e : (2 : Nat) ^ (10 : UInt32).toNat = 1024 := by decide
    rw [wavetables_setup_ushift _ _ (by decide), UInt16.toNat_toUInt32, e]
  refine ⟨by omega, by omega, ?_, range, ?_⟩
  · rw [wavetables_setup_succ _ (by omega)]
    omega
  · unfold WavetablesSetup.lineHeld
    have halved := wavetables_setup_shift_one (WavetablesSetup.smoothed previous param0)
    rw [Int32.toInt_toInt16, halved, Int.bmod_eq_of_le (by omega) (by omega)]
    omega

/-- The paraphonic engine reads its chord and the one after it inside the 17 chords, and the first parameter's
wave and the one after it inside the 33-entry short line, for parameters from 0 to 32767.
Why it matters: both are C arrays read without a check; the 17th chord and 33rd wave are there for the read
past the last entry. -/
theorem wavetables_setup_paraphonic_in_table (param0 param1 : Int16) (nonneg0 : 0 ≤ param0.toInt)
    (nonneg1 : 0 ≤ param1.toInt) :
    (WavetablesSetup.chordIndex param1 + 1).toNat ≤ 16 ∧
      ((param0.toInt32 >>> 10).toUInt32 + 1).toNat ≤ 32 := by
  have hi0 := Int16.toInt_le param0
  have hi1 := Int16.toInt_le param1
  have top : Int16.maxValue.toInt = 32767 := by decide
  have chord := wavetables_setup_shift_eleven param1.toInt32
  rw [wavetables_setup_param] at chord
  have chordValue := wavetables_setup_toUInt32_of_nonneg (param1.toInt32 >>> 11) (by rw [chord]; omega)
  have wave := wavetables_setup_shift_ten param0.toInt32
  rw [wavetables_setup_param] at wave
  have waveValue := wavetables_setup_toUInt32_of_nonneg (param0.toInt32 >>> 10) (by rw [wave]; omega)
  unfold WavetablesSetup.chordIndex
  rw [wavetables_setup_succ _ (by omega), wavetables_setup_succ _ (by omega)]
  omega

/-- A wave numbered up to 255 reads its two bytes at any halved phase inside the 33024-byte bank of 129-byte
waves (`wt_waves`, `WT_WAVES_SIZE` in `resources.h`). The selection tables above hold numbers up to 255.
Why it matters: the bank is read without a check through `Wavetables.waveByte`, which adds the wave's offset
to the byte's index; 256 waves of 129 bytes is exactly the bank. -/
theorem wavetables_setup_wave_in_bank (wave phase : UInt32) (selected : wave.toNat ≤ 255) :
    wave.toNat * 129 + (Analog.tableIndex (phase >>> 1) + 1).toNat ≤ 33023 := by
  have := tables_wave_reads_inside_129 phase
  omega

/-- Every detuned voice of the paraphonic engine steps below half a cycle per sample
(`pitch_increment_bounded`).
Why it matters: the detune is added to the pitch before the table's clamp, so none of the four voices runs
past Nyquist. -/
theorem wavetables_setup_increments_half_cycle (pitch param1 : Int16) (voice : UInt32) :
    (WavetablesSetup.voiceIncrement pitch param1 voice).toNat < 2 ^ 31 :=
  pitch_increment_bounded _
