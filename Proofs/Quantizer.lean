import Firmware.Quantizer

/-- The check below, with the scale split as `high * 64 + low` so the computer check stays shallow. -/
private theorem quantizer_scale_has_a_neighbour_split :
    ∀ high, high < 64 → ∀ low, low < 64 → high * 64 + low ≠ 0 → ∀ pitch, pitch < 12 →
      ∃ dist, dist < 7 ∧
        ((high * 64 + low).testBit ((pitch + dist) % 12) = true ∨
         (high * 64 + low).testBit ((pitch + 12 - dist) % 12) = true) := by
  decide +kernel

/-- Every non-empty scale has a note at most 6 semitones from any pitch class, going down or up around
the octave. Checked for all 4095 scales and 12 pitch classes. -/
private theorem quantizer_every_scale_has_a_neighbour :
    ∀ mask, mask < 4096 → mask ≠ 0 → ∀ pitch, pitch < 12 →
      ∃ dist, dist < 7 ∧
        (mask.testBit ((pitch + dist) % 12) = true ∨ mask.testBit ((pitch + 12 - dist) % 12) = true) := by
  intro mask small notEmpty pitch below
  have split : mask = mask / 64 * 64 + mask % 64 := by omega
  rw [split]
  exact quantizer_scale_has_a_neighbour_split (mask / 64) (by omega) (mask % 64) (by omega)
    (by omega) pitch below

/-- A hit at distance `dist` below or above `note`, in the scale. -/
private def Quantizer.Found (mask note dist found : Nat) : Prop :=
  (dist ≤ note ∧ found = note - dist ∨ found = note + dist) ∧ Quantizer.inScale mask found = true

/-- A distance that returns a note returns an in-scale note at that distance. -/
private theorem quantizer_at_some (mask note dist found : Nat)
    (h : Quantizer.at mask note dist = some found) : Quantizer.Found mask note dist found := by
  unfold Quantizer.at at h
  split at h
  · rename_i hit
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hit
    cases h
    exact ⟨Or.inl ⟨hit.1, rfl⟩, hit.2⟩
  · split at h
    · rename_i hit
      cases h
      exact ⟨Or.inr rfl, hit⟩
    · cases h

/-- A distance that returns nothing has no in-scale note below or above. -/
private theorem quantizer_at_none (mask note dist : Nat) (h : Quantizer.at mask note dist = none) :
    ¬ ((dist ≤ note ∧ Quantizer.inScale mask (note - dist) = true) ∨
        Quantizer.inScale mask (note + dist) = true) := by
  unfold Quantizer.at at h
  intro found
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i below above
      rcases found with ⟨hd, hs⟩ | hs
      · exact below (by simpa [hd] using hs)
      · exact above hs

/-- If some distance in `dist ≤ e < dist + tries` has a note in the scale, the search returns an in-scale note
found at such a distance. -/
private theorem quantizer_search_finds (mask note : Nat) :
    ∀ tries dist, (∃ e, dist ≤ e ∧ e < dist + tries ∧
        ((e ≤ note ∧ Quantizer.inScale mask (note - e) = true) ∨ Quantizer.inScale mask (note + e) = true)) →
      ∃ e, dist ≤ e ∧ e < dist + tries ∧
        Quantizer.Found mask note e (Quantizer.search mask note tries dist) := by
  intro tries
  induction tries with
  | zero => intro dist ⟨e, low, high, _⟩; omega
  | succ tries ih =>
    intro dist ⟨e, low, high, hit⟩
    unfold Quantizer.search
    cases h : Quantizer.at mask note dist with
    | some found => exact ⟨dist, Nat.le_refl _, by omega, quantizer_at_some _ _ _ _ h⟩
    | none =>
      have miss := quantizer_at_none mask note dist h
      have later : dist + 1 ≤ e := by
        rcases Nat.lt_or_ge dist e with lt | ge
        · omega
        · exact absurd (by rw [show e = dist by omega] at hit; exact hit) miss
      obtain ⟨f, low', high', found⟩ := ih (dist + 1) ⟨e, later, by omega, hit⟩
      exact ⟨f, by omega, by omega, found⟩

/-- A note already in the scale is unchanged by `snap`.
Why it matters: quantizing an in-key melody changes nothing. -/
theorem quantizer_snap_keeps_scale_notes (mask note : Nat) (inside : Quantizer.inScale mask note = true) :
    Quantizer.snap mask note = note := by
  unfold Quantizer.snap Quantizer.search Quantizer.at
  simp [inside]

/-- For a non-empty scale and a note of at least 6, `snap` returns a note of the scale found at some
distance below 7. -/
private theorem quantizer_snap_found (mask note : Nat) (small : mask < 4096) (notEmpty : mask ≠ 0)
    (low : 6 ≤ note) : ∃ dist, dist < 7 ∧ Quantizer.Found mask note dist (Quantizer.snap mask note) := by
  obtain ⟨dist, near, scale⟩ :=
    quantizer_every_scale_has_a_neighbour mask small notEmpty (note % 12) (Nat.mod_lt _ (by omega))
  have hit : ∃ e, 0 ≤ e ∧ e < 0 + 7 ∧
      ((e ≤ note ∧ Quantizer.inScale mask (note - e) = true) ∨ Quantizer.inScale mask (note + e) = true) := by
    refine ⟨dist, Nat.zero_le _, by omega, ?_⟩
    unfold Quantizer.inScale
    rcases scale with up | down
    · exact Or.inr (by rwa [show (note + dist) % 12 = (note % 12 + dist) % 12 by omega])
    · exact Or.inl ⟨by omega, by rwa [show (note - dist) % 12 = (note % 12 + 12 - dist) % 12 by omega]⟩
  obtain ⟨e, _, high, found⟩ := quantizer_search_finds mask note 7 0 hit
  exact ⟨e, by omega, found⟩

/-- `snap` gives a note of the scale, for a non-empty 12-bit mask and a note of at least 6 (so the 6-semitone
search down cannot run off the bottom).
Why it matters: the lane never plays a note outside the chosen key. -/
theorem quantizer_snap_in_scale (mask note : Nat) (small : mask < 4096) (notEmpty : mask ≠ 0)
    (low : 6 ≤ note) : Quantizer.inScale mask (Quantizer.snap mask note) = true := by
  obtain ⟨_, _, _, inside⟩ := quantizer_snap_found mask note small notEmpty low
  exact inside

/-- `snap` moves a note at most 6 semitones (same conditions as above).
Why it matters: quantizing keeps the shape of the melody. -/
theorem quantizer_snap_is_near (mask note : Nat) (small : mask < 4096) (notEmpty : mask ≠ 0)
    (low : 6 ≤ note) : Quantizer.snap mask note ≤ note + 6 ∧ note ≤ Quantizer.snap mask note + 6 := by
  obtain ⟨dist, near, ⟨moved, _⟩⟩ := quantizer_snap_found mask note small notEmpty low
  omega

/-- An octave up, the scale looks the same. -/
private theorem quantizer_in_scale_octave (mask n : Nat) : Quantizer.inScale mask (n + 12) = Quantizer.inScale mask n := by
  unfold Quantizer.inScale; rw [Nat.add_mod_right]

/-- A distance search an octave up finds the note an octave up, as long as the distance fits under the note. -/
private theorem quantizer_at_octave (mask n d : Nat) (fits : d ≤ n) :
    Quantizer.at mask (n + 12) d = (Quantizer.at mask n d).map (· + 12) := by
  unfold Quantizer.at
  have below : n + 12 - d = n - d + 12 := by omega
  rw [below, quantizer_in_scale_octave, show n + 12 + d = n + d + 12 by omega, quantizer_in_scale_octave]
  simp only [show d ≤ n + 12 from by omega, fits, decide_true, Bool.true_and]
  split
  · rfl
  · split <;> rfl

/-- The search an octave up finds the note an octave up, while every distance it tries fits under the note. -/
private theorem quantizer_search_octave (mask n : Nat) : ∀ tries d, d + tries ≤ n + 1 →
    Quantizer.search mask (n + 12) tries d = Quantizer.search mask n tries d + 12 := by
  intro tries
  induction tries with
  | zero => intro d _; rfl
  | succ t ih =>
    intro d fits
    unfold Quantizer.search
    rw [quantizer_at_octave mask n d (by omega)]
    cases Quantizer.at mask n d with
    | some found => rfl
    | none => simp only [Option.map_none]; exact ih (d + 1) (by omega)

/-- Snapping a note an octave up gives the snapped note an octave up, for notes of at least 6. -/
private theorem quantizer_snap_octave (mask n : Nat) (low : 6 ≤ n) :
    Quantizer.snap mask (n + 12) = Quantizer.snap mask n + 12 :=
  quantizer_search_octave mask n 7 0 (by omega)

/-- The check, with the scale split so the computer check stays shallow: within an octave, the next note up
never snaps lower. -/
private theorem quantizer_monotone_split :
    ∀ high, high < 64 → ∀ low, low < 64 → high * 64 + low ≠ 0 → ∀ a, a < 12 →
      Quantizer.snap (high * 64 + low) (a + 6) ≤ Quantizer.snap (high * 64 + low) (a + 7) := by
  decide +kernel

/-- For every non-empty scale, the next note up from a note of 6 to 17 never snaps lower. -/
private theorem quantizer_monotone_next (mask a : Nat) (small : mask < 4096) (notEmpty : mask ≠ 0)
    (low : 6 ≤ a) (high : a < 18) : Quantizer.snap mask a ≤ Quantizer.snap mask (a + 1) := by
  have split : mask = mask / 64 * 64 + mask % 64 := by omega
  have := quantizer_monotone_split (mask / 64) (by omega) (mask % 64) (by omega) (by omega) (a - 6) (by omega)
  rw [show a - 6 + 6 = a by omega, show a - 6 + 7 = a + 1 by omega] at this
  rw [split]; exact this

/-- Octaves up, the snap moves by octaves. -/
private theorem quantizer_snap_octaves (mask base : Nat) (low : 6 ≤ base) : ∀ j,
    Quantizer.snap mask (base + 12 * j) = Quantizer.snap mask base + 12 * j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show base + 12 * (j + 1) = (base + 12 * j) + 12 by omega, quantizer_snap_octave mask _ (by omega), ih]
    omega

/-- The next note up never snaps lower, for any note of at least 6: the octave check, moved by octaves. -/
private theorem quantizer_monotone_step (mask a : Nat) (small : mask < 4096) (notEmpty : mask ≠ 0) (low : 6 ≤ a) :
    Quantizer.snap mask a ≤ Quantizer.snap mask (a + 1) := by
  have aEq : a = (a - 6) % 12 + 6 + 12 * ((a - 6) / 12) := by have := Nat.div_add_mod (a - 6) 12; omega
  have next := quantizer_monotone_next mask ((a - 6) % 12 + 6) small notEmpty (by omega) (by omega)
  rw [aEq, quantizer_snap_octaves mask _ (by omega), show (a - 6) % 12 + 6 + 12 * ((a - 6) / 12) + 1 =
    ((a - 6) % 12 + 6 + 1) + 12 * ((a - 6) / 12) by omega, quantizer_snap_octaves mask _ (by omega)]
  omega

/-- `snap` is monotone: for two notes of at least 6 and a non-empty mask, the higher never snaps below the
lower (same conditions as the other snap theorems).
Why it matters: quantizing can merge two notes onto one scale note but cannot reverse a line's direction. -/
theorem quantizer_snap_monotone (mask a b : Nat) (small : mask < 4096) (notEmpty : mask ≠ 0) (low : 6 ≤ a)
    (order : a ≤ b) : Quantizer.snap mask a ≤ Quantizer.snap mask b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have := quantizer_monotone_step mask (a + d) small notEmpty (by omega)
    rw [show a + (d + 1) = a + d + 1 by omega]
    exact Nat.le_trans (ih (by omega)) this
