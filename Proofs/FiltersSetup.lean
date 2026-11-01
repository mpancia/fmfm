import Firmware.FiltersSetup
import Proofs.BraidsData

/-!
The per-block setup of the swarm hands a cutoff pitch to the cutoff table. These theorems say the pitch is
held to 0 to 32767, so the table read stays inside the 257 entries, and that the blended coefficient never
exceeds the table's top entry.
-/

/-- The swarm's cutoff pitch is held between 0 and 32767. -/
private theorem filters_setup_hp_cutoff_range (pitch parameter : Int32) :
    0 ≤ (FiltersSetup.swarmHpCutoff pitch parameter).toInt ∧
      (FiltersSetup.swarmHpCutoff pitch parameter).toInt ≤ 32767 := by
  unfold FiltersSetup.swarmHpCutoff
  dsimp only
  generalize (if parameter < 10922 then (24 : Int32) else 12) = slope
  generalize pitch + (((parameter - 10922) * slope) >>> 5) = moved
  have zero : (0 : Int32).toInt = 0 := by decide
  have top : (32767 : Int32).toInt = 32767 := by decide
  split
  · omega
  · split
    · omega
    · rename_i notNeg notBig
      rw [Int32.not_lt, Int32.le_iff_toInt_le] at notNeg notBig
      omega

/-- A signed value between 0 and 32767 keeps its value as an unsigned one. -/
private theorem filters_setup_small_toUInt32 (p : Int32) (lo : 0 ≤ p.toInt) (hi : p.toInt ≤ 32767) :
    p.toUInt32.toNat = p.toInt.toNat := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- A cutoff pitch of 0 to 32767, shifted up 17 places, has its top byte at the pitch over 128. -/
private theorem filters_setup_index_of (p : Int32) (lo : 0 ≤ p.toInt) (hi : p.toInt ≤ 32767) :
    (Analog.tableIndex (p.toUInt32 <<< 17)).toNat = p.toInt.toNat / 128 := by
  unfold Analog.tableIndex
  rw [UInt32.toNat_shiftRight, UInt32.toNat_shiftLeft, filters_setup_small_toUInt32 p lo hi]
  have s24 : (UInt32.toNat 24 % 32) = 24 := by decide
  have s17 : (UInt32.toNat 17 % 32) = 17 := by decide
  rw [s24, s17, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The swarm's high-pass reads two neighbouring entries of the 257-entry cutoff table, both inside it, for
every pitch and parameter.
Why it matters: the cutoff pitch is the oscillator's pitch moved by the parameter, which can run far past the
table; the clamp in `swarmHpCutoff` is what keeps the read inside, and this shows it does. -/
theorem filters_setup_cutoff_in_table (pitch parameter : Int32) :
    (Analog.tableIndex ((FiltersSetup.swarmHpCutoff pitch parameter).toUInt32 <<< 17)).toNat ≤ 255 ∧
      (Analog.tableIndex ((FiltersSetup.swarmHpCutoff pitch parameter).toUInt32 <<< 17) + 1).toNat ≤ 256 := by
  have ⟨lo, hi⟩ := filters_setup_hp_cutoff_range pitch parameter
  have e := filters_setup_index_of _ lo hi
  rw [UInt32.toNat_add, e]
  have : (1 : UInt32).toNat = 1 := by decide
  rw [this, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The blend of two neighbouring entries of a rising table, by a fraction below 65536, is at most the second
entry, given the entries fit in 15 bits so the product does not wrap. -/
private theorem filters_setup_blend_le (a b frac : UInt32) (rising : a ≤ b) (small : b.toNat ≤ 32767)
    (fracSmall : frac.toNat ≤ 65535) :
    (a + (((b - a) * frac) >>> 16)).toNat ≤ b.toNat := by
  have d := UInt32.toNat_sub_of_le b a rising
  have aLe := UInt32.le_iff_toNat_le.mp rising
  have product : ((b - a) * frac).toNat = (b.toNat - a.toNat) * frac.toNat := by
    rw [UInt32.toNat_mul, d]
    apply Nat.mod_eq_of_lt
    have := Nat.mul_le_mul (Nat.sub_le_sub_right small a.toNat) fracSmall
    omega
  have shifted : (((b - a) * frac) >>> 16).toNat = (b.toNat - a.toNat) * frac.toNat / 65536 := by
    rw [UInt32.toNat_shiftRight, product]
    have : (UInt32.toNat 16 % 32) = 16 := by decide
    rw [this, Nat.shiftRight_eq_div_pow]
  have part : (b.toNat - a.toNat) * frac.toNat / 65536 ≤ b.toNat - a.toNat := by
    have := Nat.mul_le_mul_left (b.toNat - a.toNat) fracSmall
    have := Nat.div_le_div_right (c := 65536) this
    rw [Nat.mul_comm] at this
    have e : 65535 * (b.toNat - a.toNat) / 65536 ≤ b.toNat - a.toNat := by
      apply Nat.div_le_of_le_mul
      omega
    omega
  rw [UInt32.toNat_add, shifted, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The top byte of a phase is below 256. -/
private theorem filters_setup_index_lt (phase : UInt32) : (Analog.tableIndex phase).toNat < 256 := by
  unfold Analog.tableIndex
  rw [UInt32.toNat_shiftRight]
  have : (UInt32.toNat 24 % 32) = 24 := by decide
  rw [this, Nat.shiftRight_eq_div_pow]
  have := phase.toNat_lt
  omega

/-- A table of 16-bit entries that rise from one to the next across its 257 entries and never pass `top` (at
most 32767) blends to a value at most `top` at any phase (`Digital.lutAt`).
Why it matters: a cutoff or damping coefficient read this way is a positive value no larger than the table's
top entry, which is the range the filters' sample theorems take for it; the cut to 16 bits inside the blend
changes nothing. -/
theorem filters_setup_table_blend_le_top (table : UInt32 → UInt16) (phase : UInt32) (top : Nat)
    (rising : ∀ i : UInt32, i.toNat < 256 → table i ≤ table (i + 1)) (bounded : ∀ i, (table i).toNat ≤ top)
    (small : top ≤ 32767) :
    (Digital.lutAt table phase).toNat ≤ top := by
  unfold Digital.lutAt
  dsimp only
  have r : (table (Analog.tableIndex phase)).toUInt32 ≤ (table (Analog.tableIndex phase + 1)).toUInt32 := by
    rw [UInt32.le_iff_toNat_le, UInt16.toNat_toUInt32, UInt16.toNat_toUInt32]
    exact UInt16.le_iff_toNat_le.mp (rising _ (filters_setup_index_lt phase))
  have b : (table (Analog.tableIndex phase + 1)).toUInt32.toNat ≤ top := by
    rw [UInt16.toNat_toUInt32]; exact bounded _
  have frac : ((phase >>> 8) &&& 0xFFFF).toNat ≤ 65535 := by
    rw [UInt32.toNat_and]
    have := Nat.and_le_right (n := (phase >>> 8).toNat) (m := (0xFFFF : UInt32).toNat)
    have : (0xFFFF : UInt32).toNat = 65535 := by decide
    omega
  have := filters_setup_blend_le _ _ _ r (by omega) frac
  rw [UInt16.toNat_toUInt32, UInt32.toNat_toUInt16, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The swarm's high-pass coefficient is between 0 and 25078. The cutoff table's entries rise from one to the
next and the top one is 25078 (`Proofs/BraidsData.lean`, checked against `resources.cc`).
Why it matters: the coefficient multiplies the filter's band-pass state on every sample; a positive 15-bit
coefficient is the range that keeps that product in step with the original's. -/
theorem filters_setup_cutoff_in_range (pitch parameter : Int32) :
    0 ≤ (FiltersSetup.swarmCutoff pitch parameter).toInt ∧
      (FiltersSetup.swarmCutoff pitch parameter).toInt ≤ 25078 := by
  unfold FiltersSetup.swarmCutoff Percussion.svfCutoff
  generalize (FiltersSetup.swarmHpCutoff pitch parameter).toUInt32 <<< 17 = phase
  have := filters_setup_table_blend_le_top Percussion.cutoffTable phase 25078 braids_data_cutoff_rising
    braids_data_cutoff_top (by decide)
  generalize Digital.lutAt Percussion.cutoffTable phase = v at *
  have e : v.toInt32.toInt = (v.toNat : Int) := by
    show v.toBitVec.toInt = _
    rw [BitVec.toInt_eq_toNat_of_lt]
    · simp
    · simp; omega
  omega
