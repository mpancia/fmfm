import Firmware.Keys

/-- QUANT off plays the key as it is (held to the MIDI range).
Why it matters: the setting's OFF is exactly the keyboard you had. -/
theorem keys_off_is_itself (mask key note : UInt32) (midi : note ≤ 127) :
    Keys.quantize 0 mask key note = note := by
  unfold Keys.quantize
  rw [ite_eq_left rfl, UInt32.min_def]
  simp [midi]

/-- The plain number a quantized note is, in the modes that quantize. -/
private theorem keys_quantize_toNat (mode mask key note : UInt32) (on : mode ≠ 0) :
    (Keys.quantize mode mask key note).toNat = min ((min note 127 / 12).toNat * 12 + (key % 12).toNat +
      Keys.degree (mask % 4096).toNat (key % 12).toNat (Keys.white note).toNat) 127 := by
  unfold Keys.quantize
  simp only [on, ite_false]
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt]
  have := Nat.min_le_right ((min note 127 / 12).toNat * 12 + (key % 12).toNat +
    Keys.degree (mask % 4096).toNat (key % 12).toNat (Keys.white note).toNat) 127
  omega

/-- A quantized note is a MIDI note, whatever the mode, mask, key and note.
Why it matters: a degree high in the scale from the top of the keyboard is held at 127, not wrapped. -/
theorem keys_in_range (mode mask key note : UInt32) : Keys.quantize mode mask key note ≤ 127 := by
  by_cases on : mode = 0
  · subst on; unfold Keys.quantize; rw [ite_eq_left rfl, UInt32.min_def]; split
    · assumption
    · exact UInt32.le_refl _
  · rw [UInt32.le_iff_toNat_le, keys_quantize_toNat mode mask key note on]
    have l : (127 : UInt32).toNat = 127 := by decide
    rw [l]; exact Nat.min_le_right _ _

/-- A degree of a non-empty mask is one of its offsets, an octave or more up as the degree goes round. -/
private theorem keys_degree_in_mask (mask root k : Nat) (some : (Keys.offsets mask root).length ≠ 0) :
    mask.testBit ((root + Keys.degree mask root k) % 12) = true := by
  simp only [Keys.degree, some, ite_false]
  have mem : (Keys.offsets mask root).getD (k % (Keys.offsets mask root).length) 0 ∈ Keys.offsets mask root :=
      by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.mod_lt _ (Nat.pos_of_ne_zero some))]
    exact List.getElem_mem _
  have inScale := (List.mem_filter.mp mem).2
  try simp only [decide_eq_true_eq] at inScale
  rw [← Nat.add_assoc, Nat.add_mul_mod_self_left]
  exact inScale

/-- A non-empty 12-bit mask has an offset above any root. -/
private theorem keys_offsets_some (mask root : Nat) (small : mask < 4096) (some : mask ≠ 0) (r12 : root <
    12) :
    (Keys.offsets mask root).length ≠ 0 := by
  intro empty
  apply some
  have none : ∀ d ∈ List.range 12, ¬ mask.testBit ((root + d) % 12) = true := by
    intro d mem h
    have : d ∈ Keys.offsets mask root := List.mem_filter.mpr ⟨mem, by simpa using h⟩
    rw [List.length_eq_zero_iff.mp empty] at this
    exact absurd this List.not_mem_nil
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.zero_testBit]
  by_cases lt : i < 12
  · have := none ((i + 12 - root) % 12) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
    rw [show (root + (i + 12 - root) % 12) % 12 = i by omega] at this
    exact Bool.eq_false_of_ne_true this
  · apply Nat.testBit_lt_two_pow
    calc mask < 4096 := small
      _ = 2 ^ 12 := by rfl
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)

/-- With QUANT on and a non-empty mask, every quantized note below the top is a note of the mask: the pitch
class of what plays is in the scale or the chord.
Why it matters: SCALE and CHORD keep you in: whatever key you press, the note that sounds is in the lane's
scale (or on the chord of the moment); the keyboard cannot play a wrong note. -/
theorem keys_in_scale (mode mask key note : UInt32) (on : mode ≠ 0) (some : (mask % 4096).toNat ≠ 0)
    (below : (Keys.quantize mode mask key note).toNat < 127) :
    (mask % 4096).toNat.testBit ((Keys.quantize mode mask key note).toNat % 12) = true := by
  have m4096 : (mask % 4096).toNat < 4096 := by rw [UInt32.toNat_mod]; exact Nat.mod_lt _ (by decide)
  have k12 : (key % 12).toNat < 12 := by rw [UInt32.toNat_mod]; exact Nat.mod_lt _ (by decide)
  have inMask := keys_degree_in_mask (mask % 4096).toNat (key % 12).toNat (Keys.white note).toNat
    (keys_offsets_some _ _ m4096 some k12)
  rw [keys_quantize_toNat mode mask key note on] at below ⊢
  generalize Keys.degree (mask % 4096).toNat (key % 12).toNat (Keys.white note).toNat = degree at *
  have under : min ((min note 127 / 12).toNat * 12 + (key % 12).toNat + degree) 127 =
      (min note 127 / 12).toNat * 12 + (key % 12).toNat + degree := by
    rw [Nat.min_def]; split
    · rfl
    · rw [Nat.min_def] at below; split at below <;> omega
  rw [under]
  rw [show (min note 127 / 12).toNat * 12 + (key % 12).toNat + degree =
    (key % 12).toNat + degree + 12 * (min note 127 / 12).toNat by omega, Nat.add_mul_mod_self_left]
  exact inMask

/-- The offsets of a mask are sorted: a filtered range. -/
private theorem keys_offsets_sorted (mask root i j : Nat) (lt : i < j) (hj : j < (Keys.offsets mask
    root).length) :
    (Keys.offsets mask root)[i]'(by omega) < (Keys.offsets mask root)[j] := by
  have pw : (Keys.offsets mask root).Pairwise (· < ·) := List.pairwise_lt_range.sublist List.filter_sublist
  exact (List.pairwise_iff_getElem.mp pw) i j (by omega) hj lt

/-- Every offset is below an octave. -/
private theorem keys_offset_lt (mask root i : Nat) (hi : i < (Keys.offsets mask root).length) :
    (Keys.offsets mask root)[i] < 12 :=
  List.mem_range.mp (List.mem_filter.mp (List.getElem_mem hi)).1

/-- Degrees rise with the white key, for every mask and root. -/
private theorem keys_degree_mono (mask root k l : Nat) (le : k ≤ l) :
    Keys.degree mask root k ≤ Keys.degree mask root l := by
  simp only [Keys.degree]
  split
  · exact le
  · rename_i some
    have npos := Nat.pos_of_ne_zero some
    generalize hn : (Keys.offsets mask root).length = n at *
    have bk : k % n < (Keys.offsets mask root).length := by rw [hn]; exact Nat.mod_lt _ npos
    have bl : l % n < (Keys.offsets mask root).length := by rw [hn]; exact Nat.mod_lt _ npos
    have gk : (Keys.offsets mask root).getD (k % n) 0 = (Keys.offsets mask root)[k % n]'bk := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl
    have gl : (Keys.offsets mask root).getD (l % n) 0 = (Keys.offsets mask root)[l % n]'bl := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl
    rw [gk, gl]
    have ak := keys_offset_lt mask root (k % n) (by rw [hn]; exact Nat.mod_lt _ npos)
    have al := keys_offset_lt mask root (l % n) (by rw [hn]; exact Nat.mod_lt _ npos)
    have qk := Nat.div_add_mod k n
    have ql := Nat.div_add_mod l n
    rcases Nat.lt_or_ge (k / n) (l / n) with lt | ge
    · have : 12 * (k / n) + 12 ≤ 12 * (l / n) := by omega
      omega
    · have same : k / n = l / n := by
        have := Nat.div_le_div_right (c := n) le; omega
      have mle : k % n ≤ l % n := by
        rw [same] at qk
        have := Nat.mul_le_mul_left n (Nat.le_refl (l / n)); omega
      rcases Nat.lt_or_ge (k % n) (l % n) with mlt | meq
      · have := keys_offsets_sorted mask root (k % n) (l % n) mlt (by rw [hn]; exact Nat.mod_lt _ npos); omega
      · have e : k % n = l % n := by omega
        simp only [e]; omega

/-- Checked for every pair of pitch classes in order: the white key rises with them. -/
private theorem keys_white_mono : ∀ a : Fin 12, ∀ b : Fin 12, a.val ≤ b.val →
    (Keys.white a.val.toUInt32).toNat ≤ (Keys.white b.val.toUInt32).toNat := by
  decide +kernel

/-- Within an octave the keyboard stays in order: a higher key never plays a lower note, in any mode.
Why it matters: a run up the white keys is a run up the scale; quantizing cannot turn a rising line into a
falling one. (Across an octave it can, by design, for a scale of fewer than seven notes: the white keys past
its last degree go round into the next octave.) -/
theorem keys_keep_order (mode mask key a b : UInt32) (order : a ≤ b) (midi : b ≤ 127)
    (sameOctave : a / 12 = b / 12) :
    Keys.quantize mode mask key a ≤ Keys.quantize mode mask key b := by
  by_cases on : mode = 0
  · subst on; unfold Keys.quantize; rw [ite_eq_left rfl, ite_eq_left rfl]
    have ma : min a 127 = a := by rw [UInt32.min_def]; simp [UInt32.le_trans order midi]
    have mb : min b 127 = b := by rw [UInt32.min_def]; simp [midi]
    rw [ma, mb]; exact order
  · have ma : min a 127 = a := by rw [UInt32.min_def]; simp [UInt32.le_trans order midi]
    have mb : min b 127 = b := by rw [UInt32.min_def]; simp [midi]
    rw [UInt32.le_iff_toNat_le, keys_quantize_toNat mode mask key a on,
      keys_quantize_toNat mode mask key b on, ma, mb, sameOctave]
    have ha := UInt32.toNat_mod a 12; have hb := UInt32.toNat_mod b 12
    have aq := UInt32.toNat_div a 12; have bq := UInt32.toNat_div b 12
    have o := UInt32.toNat_inj.mpr sameOctave
    rw [aq, bq] at o
    have le := UInt32.le_iff_toNat_le.mp order
    have l12 : (12 : UInt32).toNat = 12 := by decide
    rw [l12] at o
    have pc : a.toNat % 12 ≤ b.toNat % 12 := by
      have := Nat.div_add_mod a.toNat 12; have := Nat.div_add_mod b.toNat 12; omega
    have same : ∀ x : UInt32, Keys.white x = Keys.white (x.toNat % 12).toUInt32 := by
      intro x
      have e : (x.toNat % 12).toUInt32 % 12 = x % 12 := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_mod, UInt32.toNat_ofNat', l12, Nat.mod_eq_of_lt (show x.toNat % 12 < 2 ^ 32 by
          have := Nat.mod_lt x.toNat (by decide : 0 < 12); omega), Nat.mod_mod, UInt32.toNat_mod, l12]
      unfold Keys.white
      rw [e]
    have wa := same a
    have wb := same b
    rw [wa, wb]
    have w := keys_white_mono ⟨a.toNat % 12, Nat.mod_lt _ (by decide)⟩ ⟨b.toNat % 12, Nat.mod_lt _ (by
        decide)⟩ pc
    dsimp only at w
    have d := keys_degree_mono (mask % 4096).toNat (key % 12).toNat _ _ w
    omega
