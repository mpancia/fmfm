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

/-- A phase reads two neighbouring entries of a 257-entry table, both inside it, for any phase.
Why it matters: the sine, bell, cutoff, damping and comb tables all have 257 entries, so every blend of them
(`Analog.sineAt`, `Digital.lutAt`, `Analog.buzz`) stays inside without a check. -/
theorem tables_phase_reads_inside_257 (phase : UInt32) :
    (Analog.tableIndex phase).toNat ≤ 256 ∧ (Analog.tableIndex phase + 1).toNat ≤ 256 := by
  have := tables_index_lt phase
  rw [tables_succ_toNat _ (by omega)]
  omega

/-- A 16-bit index reads two neighbouring entries of a 257-entry wave shaper, both inside it.
Why it matters: the overdrive and fold shapers have 257 entries; `Analog.shape` is safe for any index
below 65536, which is why its callers mask or bound what they pass. -/
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
Why it matters: without the clamp to 16383 a high note would read past them. -/
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
Why it matters: Braids' waves are 129 bytes, half what the phase could address; the halving keeps the read
inside. -/
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

/-- A wave phase, halved and then masked to fewer steps as the wave line's rough reading does, reads inside
a 129-byte wave.
Why it matters: the mask can only lower the phase, so the rough reading stays inside like the plain one
(`tables_wave_reads_inside_129`), for any mask. -/
theorem tables_wave_line_reads_inside_129 (phase mask : UInt32) :
    (Analog.tableIndex ((phase >>> 1) &&& mask) + 1).toNat ≤ 128 := by
  unfold Analog.tableIndex
  have halved : (phase >>> 1).toNat < 2 ^ 31 := by
    rw [UInt32.toNat_shiftRight]
    have : (UInt32.toNat 1 % 32) = 1 := by decide
    rw [this, Nat.shiftRight_eq_div_pow]
    have := phase.toNat_lt
    omega
  have masked : ((phase >>> 1) &&& mask).toNat ≤ (phase >>> 1).toNat := by
    rw [UInt32.toNat_and]
    exact Nat.and_le_left
  have shifted : (((phase >>> 1) &&& mask) >>> 24).toNat = ((phase >>> 1) &&& mask).toNat / 2 ^ 24 := by
    rw [UInt32.toNat_shiftRight]
    have : (UInt32.toNat 24 % 32) = 24 := by decide
    rw [this, Nat.shiftRight_eq_div_pow]
  rw [tables_succ_toNat _ (by omega), shifted]
  omega

/-- A formant phase and an amplitude of 0 to 15 read inside the 256-entry formant tables (16 phases by 16
amplitudes).
Why it matters: the vowel's formant amplitudes are 4-bit by construction of its data, so no phase can read
past the formant sine or square table. -/
theorem tables_formant_reads_inside_256 (phase amp : UInt32) (nibble : amp.toNat ≤ 15) :
    (((phase >>> 24) &&& 0xF0) ||| amp).toNat ≤ 255 := by
  rw [UInt32.toNat_or, UInt32.toNat_and, UInt32.toNat_shiftRight]
  have mask : UInt32.toNat 0xF0 = 240 := by decide
  have places : UInt32.toNat 24 % 32 = 24 := by decide
  rw [mask, places]
  have high := Nat.and_le_right (n := phase.toNat >>> 24) (m := 240)
  have := Nat.or_lt_two_pow (n := 8) (x := phase.toNat >>> 24 &&& 240) (y := amp.toNat) (by omega) (by omega)
  omega
