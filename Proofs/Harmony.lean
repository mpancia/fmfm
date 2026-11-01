import Firmware.Harmony

/-- Checked for every scale, key, chord root and follow mode: the mask is never empty and fits in 12 bits. -/
private theorem harmony_every_mask_ok :
    ∀ scale, scale < 14 → ∀ key, key < 12 → ∀ root, root < 12 → ∀ follow, follow < 3 →
      Harmony.laneMask scale key root follow ≠ 0 ∧ Harmony.laneMask scale key root follow < 4096 := by
  decide +kernel

/-- Checked likewise: with either chord follow, every note of the chord is a note of the key's scale. -/
private theorem harmony_every_chord_in_key :
    ∀ scale, scale < 14 → ∀ key, key < 12 → ∀ root, root < 12 → ∀ follow, follow < 3 →
      Harmony.laneMask scale key root follow &&& Harmony.laneMask scale key 0 0 =
        Harmony.laneMask scale key root follow := by
  decide +kernel

/-- Checked for every scale, progression and chord: the root is a note of the scale and below an octave. -/
private theorem harmony_every_root_in_scale :
    ∀ scale, scale < 14 → ∀ p, p < 8 → ∀ s, s < 4 →
      (Harmony.scale scale).testBit (Harmony.chordRoot scale p s) = true ∧ Harmony.chordRoot scale p s < 12 := by
  decide +kernel

/-- Checked likewise: with chord follow on a progression's chord, the chord root itself is one of the lane's
notes. -/
private theorem harmony_every_chord_has_root :
    ∀ scale, scale < 14 → ∀ key, key < 12 → ∀ p, p < 8 → ∀ s, s < 4 → ∀ follow, follow < 3 →
      (Harmony.laneMask scale key (Harmony.chordRoot scale p s) follow).testBit
        ((key + Harmony.chordRoot scale p s) % 12) = true := by
  decide +kernel

/-- The mask handed to a lane always has at least one note and fits in 12 bits, for every scale, key, chord
and follow mode the firmware offers.
Why it matters: `lane_note_in_scale` needs a non-empty 12-bit scale; this is what makes that promise hold for
the chord-following lanes too, so a chord change can never leave a lane with nothing to play. -/
theorem harmony_mask_never_empty (scale key root follow : UInt32) :
    (harmonyMask scale key root follow).toNat ≠ 0 ∧ (harmonyMask scale key root follow).toNat < 4096 := by
  unfold harmonyMask
  have ⟨ne, small⟩ := harmony_every_mask_ok (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) (root.toNat % 12) (Nat.mod_lt _ (by decide)) (follow.toNat % 3)
    (Nat.mod_lt _ (by decide))
  generalize Harmony.laneMask (scale.toNat % 14) (key.toNat % 12) (root.toNat % 12) (follow.toNat % 3) = m
    at *
  simp [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show m < 2 ^ 32 by omega), ne, small]

/-- With chord follow, 7TH or TRIAD, every note a lane may play is a note of the key's scale, whatever chord
it is on: the chord is stacked from the key's scale at the chord root, not a shape moved to the root.
Why it matters: a chord progression played with chord follow stays in the key. (The ii chord of C major is
D F A, not D F# A; the second is what a transposed shape gave, and trying to prove this is what caught it.) -/
theorem harmony_follow_in_key (scale key root follow : UInt32) :
    (harmonyMask scale key root follow).toNat &&& (harmonyMask scale key 0 0).toNat =
      (harmonyMask scale key root follow).toNat := by
  unfold harmonyMask
  have ⟨_, s2⟩ := harmony_every_mask_ok (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) (root.toNat % 12) (Nat.mod_lt _ (by decide)) (follow.toNat % 3)
    (Nat.mod_lt _ (by decide))
  have ⟨_, s0⟩ := harmony_every_mask_ok (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) 0 (by decide) 0 (by decide)
  have inside := harmony_every_chord_in_key (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) (root.toNat % 12) (Nat.mod_lt _ (by decide)) (follow.toNat % 3)
    (Nat.mod_lt _ (by decide))
  simp only [show (0 : UInt32).toNat % 3 = 0 from rfl, show (0 : UInt32).toNat % 12 = 0 from rfl]
  generalize Harmony.laneMask (scale.toNat % 14) (key.toNat % 12) (root.toNat % 12) (follow.toNat % 3) = a at *
  generalize Harmony.laneMask (scale.toNat % 14) (key.toNat % 12) 0 0 = b at *
  simp [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega), inside]

/-- With chord follow on a chord of a progression, the chord's root is among the lane's notes, in every scale
and key (and without follow it is too, being a note of the key).
Why it matters: joined with `harmony_chord_root_in_key`, a progression's chord is a chord of the key with its
root present; a lane following it can play the root, not only upper notes of some other chord. -/
theorem harmony_progression_chord_has_root (scale key progression step follow : UInt32) :
    (harmonyMask scale key (harmonyChordRoot scale progression step) follow).toNat.testBit
      ((key.toNat % 12 + (harmonyChordRoot scale progression step).toNat) % 12) = true := by
  unfold harmonyMask harmonyChordRoot
  have ⟨_, small⟩ := harmony_every_root_in_scale (scale.toNat % 14) (Nat.mod_lt _ (by decide))
    (progression.toNat % 8) (Nat.mod_lt _ (by decide)) (step.toNat % 4) (Nat.mod_lt _ (by decide))
  have has := harmony_every_chord_has_root (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) (progression.toNat % 8) (Nat.mod_lt _ (by decide)) (step.toNat % 4)
    (Nat.mod_lt _ (by decide)) (follow.toNat % 3) (Nat.mod_lt _ (by decide))
  have ⟨_, s2⟩ := harmony_every_mask_ok (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) (Harmony.chordRoot (scale.toNat % 14) (progression.toNat % 8) (step.toNat % 4))
    small (follow.toNat % 3) (Nat.mod_lt _ (by decide))
  generalize Harmony.chordRoot (scale.toNat % 14) (progression.toNat % 8) (step.toNat % 4) = r at *
  have rn : (r.toUInt32).toNat = r := by
    simp [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show r < 2 ^ 32 by omega)]
  simp only [rn, Nat.mod_eq_of_lt small]
  generalize Harmony.laneMask (scale.toNat % 14) (key.toNat % 12) r (follow.toNat % 3) = a at *
  simp [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega)]
  rwa [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod] at has

/-- Every chord root is a note of the key's scale: whatever the progression, scale and chord, the root the
lanes move to (and the screen names) is a semitone step that the scale has, below an octave.
Why it matters: progressions are written as degrees, so 1-4-5-1 is I IV V in a major key and i iv v in a minor
one; this is the promise that a chord never lands on a note outside the key. -/
theorem harmony_chord_root_in_key (scale progression step : UInt32) :
    (Harmony.scale (scale.toNat % 14)).testBit (harmonyChordRoot scale progression step).toNat = true ∧
      (harmonyChordRoot scale progression step).toNat < 12 := by
  unfold harmonyChordRoot
  have ⟨inScale, small⟩ := harmony_every_root_in_scale (scale.toNat % 14) (Nat.mod_lt _ (by decide))
    (progression.toNat % 8) (Nat.mod_lt _ (by decide)) (step.toNat % 4) (Nat.mod_lt _ (by decide))
  generalize Harmony.chordRoot (scale.toNat % 14) (progression.toNat % 8) (step.toNat % 4) = r at *
  simp [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show r < 2 ^ 32 by omega), inScale, small]
