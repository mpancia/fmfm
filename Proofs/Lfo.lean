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

/-- A modulated value is at most 100, for any base, depth and phase.
Why it matters: an LFO cannot push a chance, level or timbre setting out of range. -/
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
      calc d.toNat * t.toNat / 32768
          ≤ d.toNat * 65535 / 32768 := Nat.div_le_div_right (Nat.mul_le_mul_left _ tri)
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

/-- `Lfo.triangle (~~~phase) = Lfo.triangle phase`: the triangle is symmetric about its peak.
Why it matters: the modulator rises and falls by the same path, with no jump at the turn. -/
theorem lfo_triangle_symmetric (phase : UInt32) : Lfo.triangle (~~~phase) = Lfo.triangle phase := by
  have bound := phase.toNat_lt
  have half : (phase >>> 15).toNat < 131072 := by
    simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; omega
  have mirror : (~~~phase >>> 15).toNat = 131071 - (phase >>> 15).toNat := by
    simp [UInt32.toNat_shiftRight, UInt32.toNat_not, Nat.shiftRight_eq_div_pow]; omega
  rw [← UInt32.toNat_inj]
  simp only [Lfo.triangle]
  generalize phase >>> 15 = p at *
  generalize ~~~phase >>> 15 = q at *
  have pLe : p ≤ 131071 := by rw [UInt32.le_iff_toNat_le]; simp; omega
  have qLe : q ≤ 131071 := by rw [UInt32.le_iff_toNat_le]; simp; omega
  split <;> split <;> rename_i a b <;>
    simp only [UInt32.lt_iff_toNat_lt] at a b <;>
    (try rw [UInt32.toNat_sub_of_le _ _ pLe]) <;> (try rw [UInt32.toNat_sub_of_le _ _ qLe]) <;>
    simp at a b ⊢ <;> omega

/-- At the middle of the swing (phase 2^30) the modulator returns the base unchanged (for
`base, depth ≤ 100`), and depth 0 never changes anything.
Why it matters: the knob's value is the centre of the motion, so an LFO does not shift the average; depth 0
gives exactly the set value. -/
theorem lfo_modulate_centred (base depth phase : UInt32) (small : base.toNat ≤ 100)
    (deep : depth.toNat ≤ 100) :
    lfoModulate base depth 1073741824 = base ∧ lfoModulate base 0 phase = base := by
  have capB : min base 100 = base := by
    rw [UInt32.min_def, ite_eq_left (by rw [UInt32.le_iff_toNat_le]; simpa)]
  have capD : min depth 100 = depth := by
    rw [UInt32.min_def, ite_eq_left (by rw [UInt32.le_iff_toNat_le]; simpa)]
  have keep : ∀ x : UInt32, x.toNat ≤ 100 → min 100 x = x := fun x h => by
    rw [UInt32.min_def]
    by_cases le : 100 ≤ x
    · rw [ite_eq_left le, ← UInt32.toNat_inj]; rw [UInt32.le_iff_toNat_le] at le; simp at le ⊢; omega
    · rw [ite_eq_right le]
  constructor
  · unfold lfoModulate Lfo.modulate Lfo.triangle
    rw [capB, capD]
    rw [show (1073741824 : UInt32) >>> 15 = 32768 by decide,
      ite_eq_left (show (32768 : UInt32) < 65536 by decide)]
    have product : (depth * 32768).toNat = depth.toNat * 32768 := by
      rw [UInt32.toNat_mul, Nat.mod_eq_of_lt]; simp; simp; omega
    have swing : depth * 32768 / 32768 = depth := by
      rw [← UInt32.toNat_inj, UInt32.toNat_div, product]; simp
    rw [swing]
    have sum : (base + depth).toNat = base.toNat + depth.toNat := by
      rw [UInt32.toNat_add, Nat.mod_eq_of_lt]; omega
    have notLow : ¬ (base + depth < depth) := by
      rw [UInt32.not_lt, UInt32.le_iff_toNat_le, sum]; omega
    rw [ite_eq_right notLow, UInt32.add_sub_cancel, keep base small]
  · unfold lfoModulate Lfo.modulate
    rw [capB, show min (0 : UInt32) 100 = 0 by decide]
    simp [keep base small]
