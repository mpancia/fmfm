import Firmware.Noise
import Firmware.Wavetables

/-!
Every table the engines read is C data behind an `extern`, read without a bounds check. These theorems say the
index the Lean code hands over is inside the table, so the trust in those accessors is only trust in the data.
-/

/-- Adding one to an index that is not at the top of the 32-bit range adds one to its value. -/
private theorem tables_succ_toNat (x : UInt32) (small : x.toNat < 4294967295) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt32.toNat_add]
  simp
  omega

/-- A signed value between 0 and 16383 keeps its value as an unsigned one. -/
private theorem tables_small_toUInt32 (p : Int32) (lo : 0 ≤ p.toInt) (hi : p.toInt ≤ 16383) :
    p.toUInt32.toNat ≤ 16383 := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- The top byte of a phase is below 256. -/
private theorem tables_index_lt (phase : UInt32) : (Analog.tableIndex phase).toNat < 256 := by
  unfold Analog.tableIndex
  rw [UInt32.toNat_shiftRight]
  have : (UInt32.toNat 24 % 32) = 24 := by decide
  rw [this, Nat.shiftRight_eq_div_pow]
  have := phase.toNat_lt
  omega

/-- A phase reads two neighbouring entries of a 257-entry table, both inside it, whatever the phase.
Why it matters: the sine, bell, cutoff, damping and comb tables all have 257 entries, so every blend of them
(`Analog.sineAt`, `Digital.lutAt`, `Analog.buzz`) stays inside its table at any phase, with no check
needed. -/
theorem tables_phase_reads_inside_257 (phase : UInt32) :
    (Analog.tableIndex phase).toNat ≤ 256 ∧ (Analog.tableIndex phase + 1).toNat ≤ 256 := by
  have := tables_index_lt phase
  rw [tables_succ_toNat _ (by omega)]
  omega

/-- A 16-bit index reads two neighbouring entries of a 257-entry wave shaper, both inside it.
Why it matters: the overdrive and fold shapers are 257 entries; `Analog.shape` is safe for any index below
65536, which is why its callers mask or bound what they pass. -/
theorem tables_shape_reads_inside_257 (index : UInt32) (small : index.toNat ≤ 65535) :
    (Analog.shapeIndex index + 1).toNat ≤ 256 := by
  unfold Analog.shapeIndex
  have shifted : (index >>> 8).toNat = index.toNat / 256 := by
    rw [UInt32.toNat_shiftRight]
    have : (UInt32.toNat 8 % 32) = 8 := by decide
    rw [this, Nat.shiftRight_eq_div_pow]
  rw [tables_succ_toNat _ (by omega), shifted]
  omega

/-- A pitch, after the resonator's clamp, reads inside the 129-entry resonator tables.
Why it matters: these are the only 129-entry tables; without the clamp to 16383 a high note would read past
them. The clamp is what makes the particle and twin-peaks resonators safe. -/
theorem tables_resonator_reads_inside_129 (pitch : Int32) :
    (Analog.tableIndex ((if pitch < 0 then 0 else if pitch > 16383 then 16383 else pitch).toUInt32 <<< 17)
      + 1).toNat ≤ 128 := by
  generalize h : (if pitch < 0 then 0 else if pitch > 16383 then 16383 else pitch) = p
  have clamped : 0 ≤ p.toInt ∧ p.toInt ≤ 16383 := by
    subst h
    split
    · simp
    · split
      · simp
      · rename_i a b
        simp only [gt_iff_lt] at b
        rw [Int32.lt_iff_toInt_lt] at a b
        simp at a b
        omega
  have bound := tables_small_toUInt32 p clamped.1 clamped.2
  unfold Analog.tableIndex
  have shifted : ((p.toUInt32 <<< 17) >>> 24).toNat =
      p.toUInt32.toNat * 2 ^ 17 / 2 ^ 24 := by
    rw [UInt32.toNat_shiftRight, UInt32.toNat_shiftLeft]
    have h17 : (UInt32.toNat 17 % 32) = 17 := by decide
    have h24 : (UInt32.toNat 24 % 32) = 24 := by decide
    rw [h17, h24, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have : p.toUInt32.toNat * 2 ^ 17 < 2 ^ 32 := by omega
    rw [Nat.mod_eq_of_lt this]
  rw [tables_succ_toNat _ (by omega), shifted]
  omega

/-- A wave phase, halved as the wavetable engines do, reads inside a 129-byte wave.
Why it matters: Braids' waves are 129 bytes, half the table size the phase could address; the halving in every
wavetable engine is what keeps the read inside the wave. -/
theorem tables_wave_reads_inside_129 (phase : UInt32) :
    (Analog.tableIndex (phase >>> 1) + 1).toNat ≤ 128 := by
  unfold Analog.tableIndex
  have shifted : ((phase >>> 1) >>> 24).toNat = phase.toNat / 2 / 2 ^ 24 := by
    rw [UInt32.toNat_shiftRight, UInt32.toNat_shiftRight]
    have h1 : (UInt32.toNat 1 % 32) = 1 := by decide
    have h24 : (UInt32.toNat 24 % 32) = 24 := by decide
    rw [h1, h24, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have := phase.toNat_lt
  rw [tables_succ_toNat _ (by omega), shifted]
  omega
