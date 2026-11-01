import Firmware.AnalogSetup

/-!
The analog oscillator's per-block setup turns a parameter into a pulse width and a pitch into a comb zone.
These theorems say the pulse edge stays inside the cycle and the zone stays inside the 15 comb tables.
-/

/-- A 16-bit value's range as a signed integer: 0 to 32767 when it is not negative. -/
private theorem analog_setup_int16_range (p : Int16) (nonneg : 0 ≤ p) : 0 ≤ p.toInt ∧ p.toInt ≤ 32767 := by
  rw [Int16.le_iff_toInt_le] at nonneg
  have := Int16.toInt_le p
  have top : Int16.maxValue.toInt = 32767 := by decide
  simp at nonneg
  omega

/-- A signed value that is not negative keeps its value as an unsigned one. -/
private theorem analog_setup_nonneg_toUInt32 (p : Int32) (lo : 0 ≤ p.toInt) :
    (p.toUInt32.toNat : Int) = p.toInt := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- A value of at most 32768, shifted left 16 places, is that value times 65536. -/
private theorem analog_setup_shift_sixteen (x : UInt32) (small : x.toNat ≤ 32768) :
    (x <<< 16).toNat = x.toNat * 65536 := by
  rw [UInt32.toNat_shiftLeft]
  simp only [UInt32.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (by omega)

/-- The square's parameter, after the clamp, is 0 to 32000 for a parameter that is not negative. -/
private theorem analog_setup_square_parameter_range (parameter : Int16) (nonneg : 0 ≤ parameter) :
    0 ≤ (AnalogSetup.squareParameter parameter).toInt ∧
      (AnalogSetup.squareParameter parameter).toInt ≤ 32000 := by
  have ⟨lo, hi⟩ := analog_setup_int16_range parameter nonneg
  unfold AnalogSetup.squareParameter
  split
  · decide
  · rename_i notHigh
    rw [Int16.not_lt, Int16.le_iff_toInt_le] at notHigh
    simp at notHigh
    rw [Int16.toInt_toInt32]
    omega

/-- The variable saw's parameter, after the clamp, is 1024 to 32767 for a parameter that is not negative. -/
private theorem analog_setup_variable_saw_parameter_range (parameter : Int16) (nonneg : 0 ≤ parameter) :
    1024 ≤ (if parameter < 1024 then (1024 : Int32) else parameter.toInt32).toInt ∧
      (if parameter < 1024 then (1024 : Int32) else parameter.toInt32).toInt ≤ 32767 := by
  have ⟨_, hi⟩ := analog_setup_int16_range parameter nonneg
  split
  · decide
  · rename_i notLow
    rw [Int16.not_lt, Int16.le_iff_toInt_le] at notLow
    simp at notLow
    rw [Int16.toInt_toInt32]
    omega

/-- For a parameter that is not negative (Braids' parameters are 0 to 32767), the square's pulse turns on
between 768/32768 and 32768/32768 of the cycle and the variable saw's second slope starts between
1024/32768 and 32767/32768 of it.
Why it matters: the sample code divides the distance to the pulse edge by the phase step to place its
correction; an edge at phase 0 would fall on the wrap and be corrected twice, and one past the cycle would
never be reached. -/
theorem analog_setup_pulse_width_in_range (parameter : Int16) (nonneg : 0 ≤ parameter) :
    (768 * 65536 ≤ (AnalogSetup.squarePulseWidth parameter).toNat ∧
      (AnalogSetup.squarePulseWidth parameter).toNat ≤ 32768 * 65536) ∧
      (1024 * 65536 ≤ (AnalogSetup.variableSawPulseWidth parameter).toNat ∧
        (AnalogSetup.variableSawPulseWidth parameter).toNat ≤ 32767 * 65536) := by
  constructor
  · have ⟨lo, hi⟩ := analog_setup_square_parameter_range parameter nonneg
    unfold AnalogSetup.squarePulseWidth
    have d : (32768 - AnalogSetup.squareParameter parameter).toInt =
        32768 - (AnalogSetup.squareParameter parameter).toInt := by
      rw [Int32.toInt_sub]
      exact Int.bmod_eq_of_le (by simp; omega) (by simp; omega)
    have kept := analog_setup_nonneg_toUInt32 _ (by rw [d]; omega)
    rw [analog_setup_shift_sixteen _ (by omega)]
    omega
  · have ⟨lo, hi⟩ := analog_setup_variable_saw_parameter_range parameter nonneg
    unfold AnalogSetup.variableSawPulseWidth
    have kept := analog_setup_nonneg_toUInt32 (if parameter < 1024 then (1024 : Int32) else parameter.toInt32)
      (by omega)
    rw [analog_setup_shift_sixteen _ (by omega)]
    omega

/-- The buzz reads two of the 15 comb tables, both inside the set, whatever the pitch and parameter.
Why it matters: the comb tables are C data read without a check; the clamp to the last zone is what keeps a
high pitch, or a pitch that was never clamped, from reading past them. -/
theorem analog_setup_buzz_zone_in_table (pitch parameter : Int16) :
    (AnalogSetup.buzzZone pitch parameter).toNat ≤ 14 ∧
      (AnalogSetup.buzzZone2 pitch parameter).toNat ≤ 14 := by
  unfold AnalogSetup.buzzZone2 AnalogSetup.buzzZone
  dsimp only
  generalize (AnalogSetup.buzzShiftedPitch pitch parameter >>> 10).toUInt32 = zone
  simp only [UInt32.le_iff_toNat_le, UInt32.reduceToNat]
  split <;> split <;> simp_all [UInt32.toNat_add] <;> omega
