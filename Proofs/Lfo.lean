import Firmware.Lfo

/-- The triangle never leaves 0 to 65535. -/
private theorem lfo_triangle_le (phase : UInt32) : (Lfo.triangle phase).toNat ≤ 65535 := by
  have bound := phase.toNat_lt
  have half : (phase >>> 15).toNat = phase.toNat / 32768 := by
    simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  simp only [Lfo.triangle]
  split
  · rename_i small
    rw [UInt32.lt_iff_toNat_lt] at small
    simp at small; omega
  · rename_i large
    rw [UInt32.not_lt, UInt32.le_iff_toNat_le] at large
    simp at large
    have le : phase >>> 15 ≤ 131071 := by rw [UInt32.le_iff_toNat_le]; simp [Nat.shiftRight_eq_div_pow]; omega
    rw [UInt32.toNat_sub_of_le _ _ le]
    simp [Nat.shiftRight_eq_div_pow] at large ⊢; omega

/-- `min x 100` is at most 100 as a number. -/
private theorem lfo_capped (x : UInt32) : (min x 100).toNat ≤ 100 := by
  rw [UInt32.min_def]
  split
  · rename_i h; rw [UInt32.le_iff_toNat_le] at h; simpa using h
  · simp

/-- A modulated value stays a percentage, 0 to 100, for any base, depth and phase.
Why it matters: a modulator can never push a lane's chance, level or timbre setting out of the range the rest
of the firmware expects, however it is set. -/
theorem lfo_modulate_in_range (base depth phase : UInt32) : (lfoModulate base depth phase).toNat ≤ 100 := by
  unfold lfoModulate Lfo.modulate
  have tri := lfo_triangle_le phase
  have hb := lfo_capped base
  have hd := lfo_capped depth
  generalize Lfo.triangle phase = t at tri
  generalize min base 100 = b at hb
  generalize min depth 100 = d at hd
  simp only []
  split
  · simp
  · rename_i notLow
    have prod : (d * t).toNat = d.toNat * t.toNat := by
      rw [UInt32.toNat_mul, Nat.mod_eq_of_lt]
      calc d.toNat * t.toNat ≤ 100 * 65535 := Nat.mul_le_mul hd tri
        _ < 2 ^ 32 := by decide
    have swing : (d * t / 32768).toNat = d.toNat * t.toNat / 32768 := by rw [UInt32.toNat_div, prod]; rfl
    have swingLe : d.toNat * t.toNat / 32768 ≤ 2 * d.toNat := by
      calc d.toNat * t.toNat / 32768 ≤ d.toNat * 65535 / 32768 := Nat.div_le_div_right (Nat.mul_le_mul_left _ tri)
        _ ≤ 2 * d.toNat := by omega
    have raised : (b + d * t / 32768).toNat = b.toNat + d.toNat * t.toNat / 32768 := by
      rw [UInt32.toNat_add, swing, Nat.mod_eq_of_lt]; omega
    rw [UInt32.not_lt, UInt32.le_iff_toNat_le, raised] at notLow
    rw [UInt32.min_def]
    split
    · simp
    · rename_i h
      rw [UInt32.not_le, UInt32.lt_iff_toNat_lt] at h
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, raised]; omega), raised] at h ⊢
      generalize d.toNat * t.toNat / 32768 = q at *
      simp at h; omega
