import Firmware.MacroSetup
import Proofs.Tables

/-!
The macro oscillator's per-block setup hands the analog oscillators their parameters, reads the interval table
of C data without a bounds check, and reads the filter cutoff table. These theorems say the parameters stay
0 to 32767 and the reads stay inside their tables.
-/

/-- A 16-bit value's range as a signed integer: 0 to 32767 when it is not negative. -/
private theorem macro_setup_int16_range (p : Int16) (nonneg : 0 ≤ p) : 0 ≤ p.toInt ∧ p.toInt ≤ 32767 := by
  rw [Int16.le_iff_toInt_le] at nonneg
  have := Int16.toInt_le p
  have top : Int16.maxValue.toInt = 32767 := by decide
  simp at nonneg
  omega

/-- An `Int32` shifted right 15 places is its value divided by 32768, rounded down. -/
private theorem macro_setup_shift_fifteen (s : Int32) : (s >>> 15).toInt = s.toInt / 32768 := by
  have : (s >>> 15).toInt = s.toInt >>> 15 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (15 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- An `Int32` shifted right 9 places is its value divided by 512, rounded down. -/
private theorem macro_setup_shift_nine (s : Int32) : (s >>> 9).toInt = s.toInt / 512 := by
  have : (s >>> 9).toInt = s.toInt >>> 9 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (9 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- An `Int32` shifted right 8 places is its value divided by 256, rounded down. -/
private theorem macro_setup_shift_eight (s : Int32) : (s >>> 8).toInt = s.toInt / 256 := by
  have : (s >>> 8).toInt = s.toInt >>> 8 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (8 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- An `Int32` shifted right one place is its value halved, rounded down. -/
private theorem macro_setup_shift_one (s : Int32) : (s >>> 1).toInt = s.toInt / 2 := by
  have : (s >>> 1).toInt = s.toInt >>> 1 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (1 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- A signed value that is not negative keeps its value as an unsigned one. -/
private theorem macro_setup_nonneg_toUInt32 (p : Int32) (lo : 0 ≤ p.toInt) :
    (p.toUInt32.toNat : Int) = p.toInt := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- A value between 0 and 32767 survives the cut to 16 bits. -/
private theorem macro_setup_keep16 (x : Int32) (lo : 0 ≤ x.toInt) (hi : x.toInt ≤ 32767) :
    x.toInt16.toInt32.toInt = x.toInt := by
  rw [Int16.toInt_toInt32, Int32.toInt_toInt16]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A fold amount, after the clamp, is between 0 and 32767. -/
private theorem macro_setup_attenuation_range (x : Int32) :
    0 ≤ (MacroSetup.attenuation x).toInt ∧ (MacroSetup.attenuation x).toInt ≤ 32767 := by
  unfold MacroSetup.attenuation
  split
  · decide
  · split
    · decide
    · rename_i notLow notHigh
      rw [Int32.not_lt, Int32.le_iff_toInt_le] at notLow notHigh
      simp at notLow notHigh
      omega

/-- The product of a parameter and a fold amount, both 0 to 32767, shifted down 15 places, is 0 to 32767
and survives the cut to 16 bits. -/
private theorem macro_setup_attenuated_range (p a : Int32) (pLo : 0 ≤ p.toInt) (pHi : p.toInt ≤ 32767)
    (aLo : 0 ≤ a.toInt) (aHi : a.toInt ≤ 32767) :
    0 ≤ ((p * a) >>> 15).toInt16.toInt32.toInt ∧ ((p * a) >>> 15).toInt16.toInt32.toInt ≤ 32767 := by
  have bound := Int.mul_le_mul pHi aHi aLo (by omega)
  have nonneg := Int.mul_nonneg pLo aLo
  have product : (p * a).toInt = p.toInt * a.toInt := by
    rw [Int32.toInt_mul]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have shifted := macro_setup_shift_fifteen (p * a)
  rw [product] at shifted
  rw [macro_setup_keep16 _ (by omega) (by omega)]
  omega

/-- Morph's parameter is between 0 and 32767. -/
private theorem macro_setup_morph_parameter_range (p0 : Int16) (nonneg : 0 ≤ p0) :
    0 ≤ (MacroSetup.morphParameter p0).toInt ∧ (MacroSetup.morphParameter p0).toInt ≤ 32767 := by
  have ⟨lo, hi⟩ := macro_setup_int16_range p0 nonneg
  unfold MacroSetup.morphParameter
  split
  · decide
  · rename_i above
    rw [Int16.not_le, Int16.lt_iff_toInt_lt] at above
    simp at above
    have d : (p0.toInt32 - 21846).toInt = p0.toInt - 21846 := by
      rw [Int32.toInt_sub, Int16.toInt_toInt32]
      exact Int.bmod_eq_of_le (by simp; omega) (by simp; omega)
    have m : ((p0.toInt32 - 21846) * 3).toInt = (p0.toInt - 21846) * 3 := by
      rw [Int32.toInt_mul, d]
      exact Int.bmod_eq_of_le (by simp; omega) (by simp; omega)
    rw [macro_setup_keep16 _ (by rw [m]; omega) (by rw [m]; omega), m]
    omega

/-- Every parameter the macro oscillator hands an analog oscillator is between 0 and 32767, given a first
parameter that is not negative (Braids' parameters are 0 to 32767): morph's pulse width and the sine and
triangle fold amounts.
Why it matters: the analog oscillators' pulse widths and fold tables are built for 0 to 32767; a negative or
oversized parameter would put a pulse edge outside the cycle or read a shaper past its end. -/
theorem macro_setup_parameters_in_range (pitch p0 : Int16) (nonneg : 0 ≤ p0) :
    (0 ≤ (MacroSetup.morphParameter p0).toInt ∧ (MacroSetup.morphParameter p0).toInt ≤ 32767) ∧
      (0 ≤ (MacroSetup.sineTriangleSineParameter pitch p0).toInt ∧
        (MacroSetup.sineTriangleSineParameter pitch p0).toInt ≤ 32767) ∧
      (0 ≤ (MacroSetup.sineTriangleTriParameter pitch p0).toInt ∧
        (MacroSetup.sineTriangleTriParameter pitch p0).toInt ≤ 32767) := by
  have ⟨lo, hi⟩ := macro_setup_int16_range p0 nonneg
  rw [← Int16.toInt_toInt32] at lo hi
  refine ⟨macro_setup_morph_parameter_range p0 nonneg, ?_, ?_⟩
  · unfold MacroSetup.sineTriangleSineParameter
    have ⟨aLo, aHi⟩ := macro_setup_attenuation_range (32767 - 6 * (pitch.toInt32 - 11776))
    exact macro_setup_attenuated_range _ _ lo hi aLo aHi
  · unfold MacroSetup.sineTriangleTriParameter
    have ⟨aLo, aHi⟩ := macro_setup_attenuation_range (32767 - 7 * (pitch.toInt32 - 10240))
    exact macro_setup_attenuated_range _ _ lo hi aLo aHi

/-- Morph's low-pass cutoff, as a pitch, is 0 to 32767 whatever the pitch and parameter, and its two reads of
the 257-entry cutoff table are inside it.
Why it matters: the filter table is C data read without a check, once per block for the morph engine. -/
theorem macro_setup_cutoff_in_table (pitch p1 : Int16) :
    (0 ≤ (MacroSetup.morphLpCutoff pitch p1).toInt ∧ (MacroSetup.morphLpCutoff pitch p1).toInt ≤ 32767) ∧
      (Analog.tableIndex ((MacroSetup.morphLpCutoff pitch p1).toUInt32 <<< 17)).toNat ≤ 256 ∧
      (Analog.tableIndex ((MacroSetup.morphLpCutoff pitch p1).toUInt32 <<< 17) + 1).toNat ≤ 256 := by
  refine ⟨?_, tables_phase_reads_inside_257 _⟩
  unfold MacroSetup.morphLpCutoff
  generalize pitch.toInt32 - (p1.toInt32 >>> 1) + 16384 = cutoff
  dsimp only
  split
  · decide
  · split
    · decide
    · rename_i notLow notHigh
      rw [Int32.not_lt, Int32.le_iff_toInt_le] at notLow notHigh
      simp at notLow notHigh
      omega

/-- The interval index of a parameter that is not negative is at most 63, the one after it at most 64. -/
private theorem macro_setup_triple_indexes_le (p : Int16) (nonneg : 0 ≤ p) :
    (MacroSetup.tripleIndex p).toNat ≤ 63 ∧ (MacroSetup.tripleIndex2 p).toNat ≤ 64 := by
  have ⟨lo, hi⟩ := macro_setup_int16_range p nonneg
  unfold MacroSetup.tripleIndex MacroSetup.tripleIndex2
  have nine := macro_setup_shift_nine p.toInt32
  have eight := macro_setup_shift_eight p.toInt32
  rw [Int16.toInt_toInt32] at nine eight
  have plus : ((p.toInt32 >>> 8) + 1).toInt = p.toInt / 256 + 1 := by
    rw [Int32.toInt_add, eight]
    exact Int.bmod_eq_of_le (by simp; omega) (by simp; omega)
  have one := macro_setup_shift_one ((p.toInt32 >>> 8) + 1)
  rw [plus] at one
  have a := macro_setup_nonneg_toUInt32 (p.toInt32 >>> 9) (by rw [nine]; omega)
  have b := macro_setup_nonneg_toUInt32 (((p.toInt32 >>> 8) + 1) >>> 1) (by rw [one]; omega)
  omega

/-- A triple oscillator's parameter, when not negative, reads two entries of the 65-entry interval table, both
inside it. Braids' parameters are 0 to 32767, so `nonneg` holds for every block; a negative one would read
before the table, which is why the limit is stated.
Why it matters: the interval table is C data read without a check, twice per block for the four triple
engines. -/
theorem macro_setup_triple_intervals_in_table (p : Int16) (nonneg : 0 ≤ p) :
    (MacroSetup.tripleIndex p).toNat < 65 ∧ (MacroSetup.tripleIndex2 p).toNat < 65 := by
  have := macro_setup_triple_indexes_le p nonneg
  omega
