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

/-- Every tick is between a third and five thirds of a straight tick, at every swing setting.
Why it matters: swing can never make a tick vanish (a zero-length tick would fire two steps at once) or
stretch one past the next eighth. -/
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

/-- A tick of the first eighth and a tick of the second add up to exactly two straight ticks, so the twelve
ticks of a pair of eighths take exactly 24 straight ticks, whatever the swing.
Why it matters: swing moves notes inside each pair of eighths and nothing else: a bar is as long as it was,
the four lanes stay in phase with each other and with a MIDI clock, and `run_clock_never_drifts` still holds
for the swung clock, tick for tick. -/
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

/-- A quarter note under swing is exactly 24 straight ticks long, at every setting, and every tick inside
it starts strictly after the one before (each is at least 3334).
Why it matters: swing is a feel, not a tempo change: a quarter note, a bar and a song take the time the
TEMPO knob says, a MIDI clock sent out would stay in step with one received, and no two ticks can fall
together. -/
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
