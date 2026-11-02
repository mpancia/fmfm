import Firmware.FmApi
import Firmware.Pitch
import Proofs.Pitch
import Proofs.Fm

/-!
Where the FM voice's Nyquist cap engages. An operator's increment is the voice's increment times its Q8
ratio, held at half a cycle a sample. These theorems say the hold is a saturation of the exact product, that
below the cap the product is exact, and that across the playable keyboard (MIDI notes up to 88, E6) no
shape's ratio reaches the cap, so what the tables say is what sounds.
-/

set_option maxRecDepth 4000

/-- The 64-bit product shifted by eight is the exact quotient: two 32-bit factors fit 64 bits. -/
private theorem fm_range_product (voiceInc ratio : UInt32) :
    ((voiceInc.toUInt64 * ratio.toUInt64) >>> 8).toNat = voiceInc.toNat * ratio.toNat / 256 := by
  have v := voiceInc.toNat_lt
  have r := ratio.toNat_lt
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt64.toNat_mul, UInt32.toNat_toUInt64,
    UInt32.toNat_toUInt64, Nat.mod_eq_of_lt]
  · rfl
  · calc voiceInc.toNat * ratio.toNat ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
      _ < 2 ^ 64 := by decide

/-- The cap is a saturation of the exact value: the increment is the product shifted by eight, or half a
cycle, whichever is smaller.
Why it matters: above the keyboard an operator holds at Nyquist instead of wrapping to a wrong pitch;
below it nothing is lost. -/
theorem fm_cap_is_a_hold (voiceInc ratio : UInt32) :
    (Fm.increment voiceInc ratio).toNat = min (voiceInc.toNat * ratio.toNat / 256) (2 ^ 31) := by
  have exact := fm_range_product voiceInc ratio
  have lit : (2147483648 : UInt64).toNat = 2147483648 := by decide
  simp only [Fm.increment]
  split
  · rename_i h
    rw [ge_iff_le, UInt64.le_iff_toNat_le, lit, exact] at h
    rw [Nat.min_eq_right h]
    decide
  · rename_i h
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h)
    rw [lit, exact] at this
    rw [UInt64.toNat_toUInt32, exact, Nat.mod_eq_of_lt (by omega), Nat.min_eq_left (by omega)]

/-- Below the cap the increment is the exact product shifted by eight: a product below 2^39 shifts to
below 2^31, so neither the hold nor the narrowing to 32 bits changes it.
Why it matters: an operator's pitch is exactly the voice's times the shape's ratio, with no rounding
beyond the Q8 shift. -/
theorem fm_increment_exact_below_cap (voiceInc ratio : UInt32)
    (small : voiceInc.toNat * ratio.toNat < 2 ^ 39) :
    (Fm.increment voiceInc ratio).toNat = voiceInc.toNat * ratio.toNat / 256 := by
  rw [fm_cap_is_a_hold]
  exact Nat.min_eq_left (by omega)

/-- The first 71 phase step entries are below half a cycle, so a quarter of an octave's shift puts them
below 2^27. -/
private theorem fm_range_low_entries_nat :
    ∀ i, i < 71 → BraidsData.oscillatorIncrement i < 2 ^ 31 := by
  decide +kernel

/-- Table entries up to index 70 are below half a cycle: the accessor's value is the copy's, which fits
32 bits there. -/
private theorem fm_range_low_entries (i : UInt32) (low : i.toNat < 71) :
    (Pitch.incrementTable i).toNat < 2 ^ 31 := by
  unfold Pitch.incrementTable
  have := fm_range_low_entries_nat i.toNat low
  simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.reducePow] at *
  omega

/-- A keyboard note's pitch, `note * 128` for `note ≤ 88`, survives the trip through `Int16` and `Int32`. -/
private theorem fm_range_note_toInt (note : Nat) (low : note ≤ 88) :
    ((note * 128 : Nat).toInt16).toInt32.toInt = (note * 128 : Nat) := by
  rw [Int16.toInt_toInt32, Int16.toInt_ofNat_of_lt (by omega)]

/-- A signed value between 1 and 49152 keeps its value as an unsigned one (as in `Proofs/Pitch.lean`). -/
private theorem fm_range_small_toUInt32 (p : Int32) (lo : 1 ≤ p.toInt) (hi : p.toInt ≤ 49152) :
    (p.toUInt32.toNat : Int) = p.toInt := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- How far below the table a keyboard note is: `16384 - note * 128`. -/
private theorem fm_range_below (note : Nat) (low : note ≤ 88) :
    (Pitch.below (note * 128 : Nat).toInt16).toNat = 16384 - note * 128 := by
  unfold Pitch.below
  have pitch := fm_range_note_toInt note low
  have start : Pitch.tableStart.toInt = 16384 := by decide
  have notAbove : ¬ ((note * 128 : Nat).toInt16.toInt32 ≥ Pitch.tableStart) := by
    rw [ge_iff_le, Int32.le_iff_toInt_le, start, pitch]; omega
  simp only [notAbove, ite_false]
  have sub : (Pitch.tableStart - (note * 128 : Nat).toInt16.toInt32).toInt = 16384 - (note * 128 : Nat) := by
    rw [Int32.toInt_sub, start, pitch, Int.bmod_eq_of_le] <;> omega
  have := fm_range_small_toUInt32 _ (by rw [sub]; omega) (by rw [sub]; omega)
  rw [sub] at this
  omega

/-- The octave count and folded pitch of a keyboard note, in terms of its distance below the table. -/
private theorem fm_range_shifts_folded (note : Nat) (low : note ≤ 88) :
    (Pitch.octaveShifts (note * 128 : Nat).toInt16).toNat = (16384 - note * 128 + 1535) / 1536 ∧
      (Pitch.folded (note * 128 : Nat).toInt16).toNat =
        (16384 - note * 128 + 1535) / 1536 * 1536 - (16384 - note * 128) := by
  have below := fm_range_below note low
  have shifts : (Pitch.octaveShifts (note * 128 : Nat).toInt16).toNat =
      (16384 - note * 128 + 1535) / 1536 := by
    unfold Pitch.octaveShifts Pitch.octave
    rw [UInt32.toNat_div, UInt32.toNat_add, below]
    simp
    omega
  refine ⟨shifts, ?_⟩
  unfold Pitch.folded Pitch.octave
  rw [UInt32.toNat_sub, UInt32.toNat_mul, shifts, below]
  simp
  omega

/-- The low four bits of a value are below 16 (as in `Proofs/Pitch.lean`). -/
private theorem fm_range_low_bits (x : UInt32) : (x &&& 0xF).toNat < 16 := by
  rw [UInt32.toNat_and]
  exact Nat.and_lt_two_pow _ (by decide : (0xF : UInt32).toNat < 2 ^ 4)

/-- A signed value between 0 and 2^31 keeps its value as an unsigned one (as in `Proofs/Pitch.lean`). -/
private theorem fm_range_nonneg_toUInt32 (p : Int32) (lo : 0 ≤ p.toInt) :
    (p.toUInt32.toNat : Int) = p.toInt := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- A value below 2^31 keeps its value as a signed 32-bit one (as in `Proofs/Pitch.lean`). -/
private theorem fm_range_small_toInt32 (x : UInt32) (below : x.toNat < 2 ^ 31) :
    x.toInt32.toInt = x.toNat := by
  have e : x.toInt32.toInt = x.toBitVec.toInt := rfl
  have n : x.toNat = x.toBitVec.toNat := rfl
  rw [e, n, BitVec.toInt_eq_toNat_cond]
  rw [n] at below
  split <;> omega

/-- An arithmetic shift by four of a signed 32-bit value divides it by 16 (as in `Proofs/Pitch.lean`). -/
private theorem fm_range_shift_four (s : Int32) : (s >>> 4).toInt = s.toInt / 16 := by
  have : (s >>> 4).toInt = s.toInt >>> 4 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (4 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- Blending two neighbouring table entries that rise by less than 2^27 gives a value at most the second
(as in `Proofs/Pitch.lean`). -/
private theorem fm_range_blend_le (a b frac : UInt32) (rising : a ≤ b) (close : b.toNat - a.toNat < 2 ^ 27)
    (small : frac.toNat < 16) :
    (a + (((b - a).toInt32 * frac.toInt32) >>> 4).toUInt32).toNat ≤ b.toNat := by
  rw [UInt32.le_iff_toNat_le] at rising
  have aLt := a.toNat_lt
  have bLt := b.toNat_lt
  have d : (b - a).toNat = b.toNat - a.toNat := by rw [UInt32.toNat_sub]; omega
  have product : ((b - a).toInt32 * frac.toInt32).toInt = ((b.toNat - a.toNat) * frac.toNat : Nat) := by
    rw [Int32.toInt_mul, fm_range_small_toInt32 _ (by omega), fm_range_small_toInt32 _ (by omega), d,
      Int.bmod_eq_of_le]
    · simp
    · have := Nat.mul_le_mul (Nat.le_of_lt_succ close) (Nat.le_of_lt_succ small); omega
    · have := Nat.mul_le_mul (Nat.le_of_lt_succ close) (Nat.le_of_lt_succ small); omega
  have quotient := fm_range_shift_four ((b - a).toInt32 * frac.toInt32)
  rw [product] at quotient
  have step : ((((b - a).toInt32 * frac.toInt32) >>> 4).toUInt32.toNat : Int) =
      (((b.toNat - a.toNat) * frac.toNat : Nat) : Int) / 16 := by
    rw [fm_range_nonneg_toUInt32 _ (by rw [quotient]; omega), quotient]
  have stepLe : ((((b - a).toInt32 * frac.toInt32) >>> 4).toUInt32.toNat : Int) ≤ b.toNat - a.toNat := by
    rw [step]
    have := Nat.mul_le_mul_left (b.toNat - a.toNat) (Nat.le_of_lt_succ small)
    have := Int.ediv_le_self 16 (Int.natCast_nonneg ((b.toNat - a.toNat) * frac.toNat))
    omega
  rw [UInt32.toNat_add]
  omega

/-- Adding one to an index that is not at the top of the 32-bit range adds one to its value. -/
private theorem fm_range_succ_toNat (x : UInt32) (small : x.toNat < 4294967295) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt32.toNat_add]
  simp
  omega

/-- A keyboard note's voice increment is below 2^27, a sixteenth of a cycle. Notes up to 79 are at least five
octaves below the table, where even its top entry shifts below 2^27; notes 80 to 88 are four octaves below
and read entries at most 70, which are below half a cycle and so shift below 2^27. -/
private theorem fm_range_keyboard_increment (note : Nat) (low : note ≤ 88) :
    (Pitch.phaseIncrement (note * 128 : Nat).toInt16).toNat < 2 ^ 27 := by
  have ⟨shifts, folded⟩ := fm_range_shifts_folded note low
  have fourBits : (4 : UInt32).toNat % 32 = 4 := by decide
  have index : (Pitch.tableIndex (note * 128 : Nat).toInt16).toNat =
      ((16384 - note * 128 + 1535) / 1536 * 1536 - (16384 - note * 128)) / 16 := by
    unfold Pitch.tableIndex
    rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, folded, fourBits]
  have inside : (Pitch.tableIndex (note * 128 : Nat).toInt16).toNat < 96 := by rw [index]; omega
  have topStep : (Pitch.topOctaveStep (note * 128 : Nat).toInt16).toNat ≤
      (Pitch.incrementTable (Pitch.tableIndex (note * 128 : Nat).toInt16 + 1)).toNat := by
    unfold Pitch.topOctaveStep
    exact fm_range_blend_le _ _ _ (braids_data_increments_rising _ inside)
      (braids_data_increments_close _ inside) (fm_range_low_bits _)
  have top := braids_data_increments_top (Pitch.tableIndex (note * 128 : Nat).toInt16 + 1)
  unfold Pitch.phaseIncrement
  dsimp only
  have thirtyTwo : (32 : UInt32).toNat = 32 := by decide
  split
  · rename_i over
    rw [ge_iff_le, UInt32.le_iff_toNat_le, thirtyTwo, shifts] at over
    omega
  · rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by rw [shifts]; omega), shifts]
    by_cases deep : note ≤ 79
    · have five : 5 ≤ (16384 - note * 128 + 1535) / 1536 := by omega
      have := Nat.pow_le_pow_right (by decide : 0 < 2) five
      have := Nat.div_le_div_left this (by decide : 0 < 2 ^ 5)
        (a := (Pitch.topOctaveStep (note * 128 : Nat).toInt16).toNat)
      omega
    · have four : (16384 - note * 128 + 1535) / 1536 = 4 := by omega
      rw [four]
      have small : (Pitch.tableIndex (note * 128 : Nat).toInt16).toNat < 65 := by rw [index]; omega
      have succ := fm_range_succ_toNat (Pitch.tableIndex (note * 128 : Nat).toInt16) (by omega)
      have entry := fm_range_low_entries (Pitch.tableIndex (note * 128 : Nat).toInt16 + 1)
        (by rw [succ]; omega)
      omega

/-- For MIDI notes 0 to 88 (up to E6, 1319 Hz) every operator's increment is the exact product of the
voice's increment and its shape's ratio, shifted by eight; the Nyquist cap never engages. The voice's
increment is `Pitch.phaseIncrement` at `note * 128` (1/128 semitones), below 2^27 there, and every ratio is
at most 16.0 (`fm_shapes_in_range`), so the product is below 2^39.
Why it matters: every FM shape's ratios are exact across the playable keyboard; above it the engine
saturates at Nyquist (`fm_cap_is_a_hold`). -/
theorem fm_no_cap_on_the_keyboard (note : Nat) (shape op : UInt32) (low : note ≤ 88) :
    (Fm.increment (Pitch.phaseIncrement (note * 128 : Nat).toInt16) (Fm.ratio shape op)).toNat =
      (Pitch.phaseIncrement (note * 128 : Nat).toInt16).toNat * (Fm.ratio shape op).toNat / 256 := by
  apply fm_increment_exact_below_cap
  have inc := fm_range_keyboard_increment note low
  have ratio := ((fm_shapes_in_range shape).1 op).1
  calc (Pitch.phaseIncrement (note * 128 : Nat).toInt16).toNat * (Fm.ratio shape op).toNat
      ≤ (2 ^ 27 - 1) * 4096 := Nat.mul_le_mul (by omega) ratio
    _ < 2 ^ 39 := by decide
