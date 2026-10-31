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

/-- A note that is already in the scale stays as it is.
Why it matters: quantizing a melody that is already in key changes nothing, so it can be repeated. -/
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

/-- `snap` gives a note of the scale, as long as the scale has at least one note and the note is at least 6
(so a search 6 semitones down cannot run off the bottom).
Why it matters: the melody can never play a note outside the key you chose. -/
theorem quantizer_snap_in_scale (mask note : Nat) (small : mask < 4096) (notEmpty : mask ≠ 0)
    (low : 6 ≤ note) : Quantizer.inScale mask (Quantizer.snap mask note) = true := by
  obtain ⟨_, _, _, inside⟩ := quantizer_snap_found mask note small notEmpty low
  exact inside

/-- `snap` never moves a note more than 6 semitones (same conditions as above).
Why it matters: quantizing keeps the shape of the melody; no note jumps by an octave. -/
theorem quantizer_snap_is_near (mask note : Nat) (small : mask < 4096) (notEmpty : mask ≠ 0)
    (low : 6 ≤ note) : Quantizer.snap mask note ≤ note + 6 ∧ note ≤ Quantizer.snap mask note + 6 := by
  obtain ⟨dist, near, ⟨moved, _⟩⟩ := quantizer_snap_found mask note small notEmpty low
  omega
