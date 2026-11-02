import Firmware.Swing

/-- `min s 100` is at most 100. -/
private theorem swing_clamped (s : UInt32) : (min s 100).toNat ≤ 100 := by
  rw [UInt32.min_def]; split <;> simp_all [UInt32.le_iff_toNat_le]

/-- The first eighth's tick as a plain number. -/
private theorem swing_first_value (s : UInt32) :
    (10000 + 6666 * min s 100 / 100 : UInt32).toNat = 10000 + 6666 * (min s 100).toNat / 100 := by
  have := swing_clamped s
  simp only [UInt32.toNat_add, UInt32.toNat_div, UInt32.toNat_mul, UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (by omega : 6666 * (min s 100).toNat < 4294967296), Nat.mod_eq_of_lt (by omega)]

/-- Every tick is between 1/3 and 5/3 of a straight tick, at every swing setting.
Why it matters: swing cannot make a tick vanish (two steps firing at once) or stretch one past the next
eighth. -/
theorem swing_tick_in_range (phase swing : UInt32) :
    3334 ≤ (Swing.tickLength phase swing).toNat ∧ (Swing.tickLength phase swing).toNat ≤ 16666 := by
  unfold Swing.tickLength
  have c := swing_clamped swing
  have f := swing_first_value swing
  split
  · rw [f]; omega
  · rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, f]; simp; omega), f]
    simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega

/-- A tick of the first eighth plus a tick of the second is exactly two straight ticks, so a pair of eighths
(12 ticks) takes exactly 24 straight ticks at any swing.
Why it matters: swing only moves notes within each pair of eighths; bar length and lane phase are
unchanged. -/
theorem swing_keeps_time (phase swing : UInt32) (first : phase.toNat < 12) :
    (Swing.tickLength phase swing).toNat + (Swing.tickLength (phase + 12) swing).toNat = 20000 := by
  unfold Swing.tickLength
  have c := swing_clamped swing
  have f := swing_first_value swing
  have second : ¬ (phase + 12) % 24 < 12 := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_mod, UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (by omega : phase.toNat + 12 < 4294967296)]
    omega
  have firstU : phase % 24 < 12 := by
    rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_mod]; simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  simp only [firstU, second, ite_true, ite_false]
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, f]; simp; omega), f]
  simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- The tick lengths only see the setting clamped to 100. -/
private theorem swing_clamp_setting (phase swing : UInt32) :
    Swing.tickLength phase swing = Swing.tickLength phase (min swing 100) := by
  unfold Swing.tickLength
  have m : min (min swing 100) 100 = min swing 100 := by
    by_cases h : swing ≤ 100
    · simp [UInt32.min_def, h]
    · simp [UInt32.min_def, h]
  rw [m]

/-- Checked for every setting: the 24 ticks of a quarter note add up to 240000, twenty-four straight ticks. -/
private theorem swing_every_quarter_exact :
    ∀ swing : Fin 101,
      (List.range 24).foldl (fun acc phase => acc + (Swing.tickLength phase.toUInt32 swing.val.toUInt32).toNat) 0
        = 240000 := by
  decide +kernel

/-- A swung quarter note is exactly 24 straight ticks long at every setting, and each tick inside it is at
least 3334 long, so ticks never coincide.
Why it matters: swing does not change the tempo, and an outgoing MIDI clock stays in step. -/
theorem swing_quarter_note_exact (swing : UInt32) :
    (List.range 24).foldl (fun acc phase => acc + (Swing.tickLength phase.toUInt32 swing).toNat) 0 = 240000 ∧
      ∀ phase, 3334 ≤ (Swing.tickLength phase swing).toNat := by
  constructor
  · have small : (min swing 100).toNat ≤ 100 := swing_clamped swing
    have := swing_every_quarter_exact ⟨(min swing 100).toNat, by omega⟩
    simp only [UInt32.ofNat_toNat] at this
    simp only [swing_clamp_setting _ swing]
    exact this
  · intro phase; exact (swing_tick_in_range phase swing).1
