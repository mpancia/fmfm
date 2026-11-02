import Firmware.PunchApi

/-! The punch-in effects (`Firmware/Punch.lean`): with no key held nothing changes, so letting go restores the
performance exactly; a transposed note stays a MIDI note; the clock never stops or runs away; the gate is open
half the time and its gain glides within bounds; the crush only ever repeats a sample; the re-strikes line up
with the beat. -/

/-- With no key held every effect is the identity: tempo 100 percent, no re-strike, note unchanged, gate open
at full gain, crush holding nothing, reverb and delay at their settings, no lane muted.
Why it matters: there is no effect state beyond the keys; releasing the last key restores the performance
exactly. -/
theorem punch_nothing_held_changes_nothing (choice shift note base lane factor tick : UInt32) (midi : note
    ≤ 127) :
    Punch.tempoPercent 0 = 100 ∧ Punch.restrike 0 choice tick = false ∧ Punch.note 0 shift note = note ∧
      Punch.gateOpen 0 choice tick = true ∧ Punch.gateTarget (Punch.gateOpen 0 choice tick) = 32768 ∧
      Punch.crushFactor 0 factor = 1 ∧ Punch.reverbAmount 0 base = base ∧ Punch.delayAmount 0 base = base ∧
      Punch.laneMuted 0 lane = false := by
  have none : ∀ k, Punch.held 0 k = false := by intro k; simp [Punch.held]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Punch.tempoPercent, none]
  · simp [Punch.restrike, Punch.stutterPeriod, none]
  · simp only [Punch.note, Punch.transpose, none, Bool.false_eq_true, ite_false, Int32.add_zero,
      Int32.zero_add]
    have small : min note 127 = note := by rw [UInt32.min_def]; simp [midi]
    rw [small]
    have v : note.toInt32.toInt = note.toNat := by
      show note.toBitVec.toInt = _
      rw [BitVec.toInt_eq_toNat_of_lt]
      · rfl
      · have := UInt32.le_iff_toNat_le.mp midi; simp at this ⊢; omega
    have hi : ¬ (note.toInt32 > 127) := by
      intro h; have := Int32.lt_iff_toInt_lt.mp h
      have l := UInt32.le_iff_toNat_le.mp midi; simp at l; rw [v] at this
      have : (127 : Int32).toInt = 127 := by decide
      omega
    have lo : ¬ (note.toInt32 < 0) := by
      intro h; have := Int32.lt_iff_toInt_lt.mp h; rw [v] at this
      have : (0 : Int32).toInt = 0 := by decide
      omega
    simp only [lo, hi, ite_false]
    show (note.toInt32).toUInt32 = note
    rfl
  · simp [Punch.gateOpen, Punch.gatePeriod, none]
  · simp [Punch.gateTarget, Punch.gateOpen, Punch.gatePeriod, none]
  · simp [Punch.crushFactor, none]
  · simp [Punch.reverbAmount, none]
  · simp [Punch.delayAmount, none]
  · simp [Punch.laneMuted, none]

/-- A punched note is at most 127, for any keys, shift and note.
Why it matters: OCTAVE and SHIFT cannot push a note past the range the voices accept (`play` drops notes above
127); edge notes are clamped instead. -/
theorem punch_note_in_range (keys shift note : UInt32) : Punch.note keys shift note ≤ 127 := by
  simp only [Punch.note]
  split
  · decide
  · split
    · decide
    · rename_i low high
      have h1 := Int32.not_lt.mp low; have h2 := Int32.not_lt.mp high
      generalize (min note 127).toInt32 + Punch.transpose keys shift = m at *
      rw [UInt32.le_iff_toNat_le, Int32.toNat_toUInt32_of_le h1]
      have := Int32.le_iff_toInt_le.mp h2
      have t : (127 : Int32).toInt = 127 := by decide
      rw [t] at this
      have c : (m.toNatClampNeg : Int) = m.toInt := by
        unfold Int32.toNatClampNeg
        have := Int32.le_iff_toInt_le.mp h1
        have z : (0 : Int32).toInt = 0 := by decide
        rw [z] at this
        omega
      show m.toNatClampNeg ≤ (127 : UInt32).toNat
      have l : (127 : UInt32).toNat = 127 := by decide
      omega

/-- The clock speed is 50, 100 or 200 percent.
Why it matters: HALF and DOUBLE cannot stop the clock or run it away. -/
theorem punch_tempo_in_range (keys : UInt32) :
    Punch.tempoPercent keys = 50 ∨ Punch.tempoPercent keys = 100 ∨ Punch.tempoPercent keys = 200 := by
  unfold Punch.tempoPercent
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)

/-- Checked: in any run of 12 ticks (from any phase), 6 are in the first half of their period; likewise 3
of 6. -/
private theorem punch_half_of_period :
    (∀ s : Fin 12, ((List.range 12).filter (fun k => decide ((s.val + k) % 12 < 6))).length = 6) ∧
      (∀ s : Fin 6, ((List.range 6).filter (fun k => decide ((s.val + k) % 6 < 3))).length = 3) := by
  constructor <;> decide +kernel

/-- A tick's place in a period of `m`, as plain numbers, for the ticks of one period that does not wrap. -/
private theorem punch_shift (start : UInt32) (noWrap : start.toNat + 12 < 2 ^ 32) (m k : Nat) (hk : k < 12)
    (hm : 0 < m) (hm12 : m ≤ 12) :
    (start + k.toUInt32) % m.toUInt32 = ((start.toNat % m + k) % m).toUInt32 := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_mod, UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat', UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show m < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show start.toNat + k < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show (start.toNat % m + k)
% m < 2 ^ 32 by
      have := Nat.mod_lt (start.toNat % m + k) hm; omega)]
  rw [Nat.mod_add_mod]

/-- Over any whole period that does not cross the tick counter's end, the gate is open for exactly half the
ticks.
Why it matters: GATE is an even square at the rate the knob says, however the period lines up with the bar. -/
theorem punch_gate_half_open (keys choice start : UInt32) (on : Punch.held keys 7 = true)
    (noWrap : start.toNat + 12 < 2 ^ 32) :
    let period := Punch.gatePeriod keys choice
    ((List.range period.toNat).filter (fun k => Punch.gateOpen keys choice (start + k.toUInt32))).length =
      period.toNat / 2 := by
  intro period
  by_cases c : choice = 0
  · have e : ∀ k ∈ List.range 12, Punch.gateOpen keys choice (start + k.toUInt32) =
        decide ((start.toNat % 12 + k) % 12 < 6) := by
      intro k mem
      have hk := List.mem_range.mp mem
      simp only [Punch.gateOpen, Punch.gatePeriod, on, c, ite_true]
      have s12 : (start + k.toUInt32) % 12 = ((start.toNat % 12 + k) % 12).toUInt32 :=
        punch_shift start noWrap 12 k hk (by decide) (by decide)
      rw [show (12 : UInt32) / 2 = 6 by decide, s12]
      simp only [show ((12 : UInt32) = 0) = False by simp, decide_false, Bool.false_or]
      have iff : (((start.toNat % 12 + k) % 12).toUInt32 < 6) ↔ ((start.toNat % 12 + k) % 12 < 6) := by
        rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat',
          Nat.mod_eq_of_lt (by have := Nat.mod_lt (start.toNat % 12 + k) (by decide : 0 < 12); omega)]
        have l : (6 : UInt32).toNat = 6 := by decide
        rw [l]
      simp only [iff]
    have pv : period.toNat = 12 := by simp [period, Punch.gatePeriod, on, c]
    rw [pv, List.filter_congr e]
    exact (punch_half_of_period.1 ⟨start.toNat % 12, Nat.mod_lt _ (by decide)⟩)
  · have e : ∀ k ∈ List.range 6, Punch.gateOpen keys choice (start + k.toUInt32) =
        decide ((start.toNat % 6 + k) % 6 < 3) := by
      intro k mem
      have hk := List.mem_range.mp mem
      simp only [Punch.gateOpen, Punch.gatePeriod, on, c, ite_true, ite_false]
      have s6 : (start + k.toUInt32) % 6 = ((start.toNat % 6 + k) % 6).toUInt32 :=
        punch_shift start noWrap 6 k (by omega) (by decide) (by decide)
      rw [show (6 : UInt32) / 2 = 3 by decide, s6]
      simp only [show ((6 : UInt32) = 0) = False by simp, decide_false, Bool.false_or]
      have iff : (((start.toNat % 6 + k) % 6).toUInt32 < 3) ↔ ((start.toNat % 6 + k) % 6 < 3) := by
        rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat',
          Nat.mod_eq_of_lt (by have := Nat.mod_lt (start.toNat % 6 + k) (by decide : 0 < 6); omega)]
        have l : (3 : UInt32).toNat = 3 := by decide
        rw [l]
      simp only [iff]
    have pv : period.toNat = 6 := by simp [period, Punch.gatePeriod, on, c]
    rw [pv, List.filter_congr e]
    exact (punch_half_of_period.2 ⟨start.toNat % 6, Nat.mod_lt _ (by decide)⟩)

/-- The gate gain stays between 0 and 32768 and moves toward its target by at most 512 a sample, landing on it
exactly.
Why it matters: a chop is a 1.5 ms slope, so GATE never clicks, and the gain never exceeds unity. -/
theorem punch_gate_glides (gain target : UInt32) (unitG : gain ≤ 32768) (unitT : target ≤ 32768) :
    Punch.gateStep gain target ≤ 32768 ∧
      (gain < target → gain < Punch.gateStep gain target ∧ Punch.gateStep gain target ≤ target) ∧
      (target < gain → target ≤ Punch.gateStep gain target ∧ Punch.gateStep gain target < gain) ∧
      (gain = target → Punch.gateStep gain target = gain) := by
  have lit : (32768 : UInt32).toNat = 32768 := by decide
  have l512 : (512 : UInt32).toNat = 512 := by decide
  have g := UInt32.le_iff_toNat_le.mp unitG; have t := UInt32.le_iff_toNat_le.mp unitT
  rw [lit] at g t
  have a : (gain + 512).toNat = gain.toNat + 512 := by
    rw [UInt32.toNat_add, l512]; exact Nat.mod_eq_of_lt (by omega)
  have d : (gain - target).toNat = gain.toNat - target.toNat ∨ target.toNat < gain.toNat ∨ target.toNat ≥
      gain.toNat := by
    omega
  unfold Punch.gateStep
  by_cases lt : gain < target
  · have lt' := UInt32.lt_iff_toNat_lt.mp lt
    rw [ite_eq_left lt, UInt32.min_def]
    by_cases le : target ≤ gain + 512
    · rw [ite_eq_left le]
      have := UInt32.le_iff_toNat_le.mp le; rw [a] at this
      refine ⟨unitT, fun _ => ⟨lt, Nat.le_refl _⟩, fun h => absurd (Nat.lt_trans (UInt32.lt_iff_toNat_lt.mp
          h) lt') (Nat.lt_irrefl _), fun h => absurd (h ▸ lt) (Nat.lt_irrefl _)⟩
    · rw [ite_eq_right le]
      have := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp le); rw [a] at this
      refine ⟨?_, fun _ => ⟨?_, ?_⟩, fun h => absurd (Nat.lt_trans (UInt32.lt_iff_toNat_lt.mp h) lt')
          (Nat.lt_irrefl _), fun h => absurd (h ▸ lt) (Nat.lt_irrefl _)⟩
      · rw [UInt32.le_iff_toNat_le, a, lit]; omega
      · rw [UInt32.lt_iff_toNat_lt, a]; omega
      · rw [UInt32.le_iff_toNat_le, a]; omega
  · rw [ite_eq_right lt]
    have nlt := UInt32.not_lt.mp lt
    have nlt' := UInt32.le_iff_toNat_le.mp nlt
    by_cases gt : target < gain
    · have gt' := UInt32.lt_iff_toNat_lt.mp gt
      rw [ite_eq_left gt]
      have sub : (gain - target).toNat = gain.toNat - target.toNat := UInt32.toNat_sub_of_le _ _ nlt
      have mn : (min (gain - target) 512).toNat = min (gain.toNat - target.toNat) 512 := by
        rw [UInt32.min_def]; split
        · rename_i h; have := UInt32.le_iff_toNat_le.mp h; rw [sub, l512] at this; rw [sub]; omega
        · rename_i h; have := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp h); rw [sub, l512] at this; rw
            [l512]; omega
      have mle : min (gain - target) 512 ≤ gain := by
        rw [UInt32.le_iff_toNat_le, mn]; omega
      have res : (gain - min (gain - target) 512).toNat = gain.toNat - min (gain.toNat - target.toNat) 512 :=
          by
        rw [UInt32.toNat_sub_of_le _ _ mle, mn]
      refine ⟨?_, fun h => absurd (Nat.lt_trans (UInt32.lt_iff_toNat_lt.mp h) gt') (Nat.lt_irrefl _), fun _
          => ⟨?_, ?_⟩, fun h => absurd (h ▸ gt) (Nat.lt_irrefl _)⟩
      · rw [UInt32.le_iff_toNat_le, res, lit]; omega
      · rw [UInt32.le_iff_toNat_le, res]; omega
      · rw [UInt32.lt_iff_toNat_lt, res]; omega
    · rw [ite_eq_right gt]
      have eq : gain = target := by
        have := UInt32.le_iff_toNat_le.mp (UInt32.not_lt.mp gt)
        exact UInt32.toNat_inj.mp (by omega)
      exact ⟨unitG, fun h => absurd h lt, fun h => absurd h gt, fun _ => rfl⟩

/-- A crushed sample is either the fresh sample or the held one.
Why it matters: CRUSH adds nothing new, so the output stays inside every bound the mix had. -/
theorem punch_crush_repeats (factor index : UInt32) (heldSample sample : Int32) :
    Punch.crushSample factor index heldSample sample = sample ∨
      Punch.crushSample factor index heldSample sample = heldSample := by
  unfold Punch.crushSample; split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A non-zero re-strike period divides the quarter note (24 ticks).
Why it matters: STUTTER and ROLL land on the beat's divisions and come back to the beat. -/
theorem punch_restrikes_on_the_beat (keys choice : UInt32) (some : Punch.stutterPeriod keys choice ≠ 0) :
    24 % Punch.stutterPeriod keys choice = 0 := by
  unfold Punch.stutterPeriod Punch.stutterChoice at *
  split <;> rename_i h3
  · decide
  · split <;> rename_i h2
    · split <;> (try split) <;> decide
    · simp [h3, h2] at some
