import Firmware.Keys
import Firmware.Harmony

/-!
QUANT CHORD on a Tonnetz walk: the lane's mask is the walk's triad turned to the key
(`harmony_walk_chord_is_triad`), so the white keys are the three chord tones and repeat an octave up.
-/

/-- Checked for every triad and key: the triad turned to the key has three offsets above the key. -/
private theorem keys_triad_offsets_three :
    ∀ t : Fin 24, ∀ key : Fin 12,
      (Keys.offsets (Harmony.rotate (Tonnetz.mask t) key) key).length = 3 := by
  decide +kernel

/-- Checked for every triad and key: the three degrees, as pitch classes, are exactly the triad's notes. -/
private theorem keys_triad_degrees_make_mask :
    ∀ t : Fin 24, ∀ key : Fin 12,
      let mask := Harmony.rotate (Tonnetz.mask t) key
      (1 <<< ((key + Keys.degree mask key 0) % 12)) ||| (1 <<< ((key + Keys.degree mask key 1) % 12)) |||
        (1 <<< ((key + Keys.degree mask key 2) % 12)) = mask := by
  decide +kernel

/-- The three-offset fact with plain `UInt32` inputs. -/
private theorem keys_triad_three (t key : UInt32) (triad : t < 24) (k12 : key < 12) :
    (Keys.offsets (Harmony.rotate (Tonnetz.mask t.toNat) key.toNat) key.toNat).length = 3 :=
  keys_triad_offsets_three ⟨t.toNat, UInt32.lt_iff_toNat_lt.mp triad⟩
    ⟨key.toNat, UInt32.lt_iff_toNat_lt.mp k12⟩

/-- A triad mask is below 4096, so `toUInt32` and back is the identity on it. -/
private theorem keys_triad_mask_roundtrip (t key : UInt32) :
    (Harmony.rotate (Tonnetz.mask t.toNat) key.toNat).toUInt32.toNat =
      Harmony.rotate (Tonnetz.mask t.toNat) key.toNat := by
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt]
  unfold Harmony.rotate
  have := Nat.and_lt_two_pow
    ((Tonnetz.mask t.toNat <<< key.toNat) ||| (Tonnetz.mask t.toNat >>> (12 - key.toNat)))
    (show 0xFFF < 2 ^ 12 by decide)
  omega

/-- With CHORD on a Tonnetz walk the lane's mask is a triad, and white key `w + 3` plays white key `w` an
octave up.
Why it matters: the white keys are the chord of the moment, three to the octave. -/
theorem keys_triad_three_an_octave (t key : UInt32) (triad : t < 24) (k12 : key < 12) :
    let mask := (Harmony.rotate (Tonnetz.mask t.toNat) key.toNat).toUInt32
    ∀ w : Fin 7, Keys.degree mask.toNat key.toNat (w.val + 3) =
      Keys.degree mask.toNat key.toNat w.val + 12 := by
  intro mask w
  have three : (Keys.offsets mask.toNat key.toNat).length = 3 := by
    show (Keys.offsets (Harmony.rotate (Tonnetz.mask t.toNat) key.toNat).toUInt32.toNat key.toNat).length = 3
    rw [keys_triad_mask_roundtrip t key]; exact keys_triad_three t key triad k12
  simp only [Keys.degree, three, show (3 : Nat) = 0 ↔ False by decide, ite_false]
  rw [show (w.val + 3) % 3 = w.val % 3 by omega, show (w.val + 3) / 3 = w.val / 3 + 1 by omega]
  omega

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

/-- With CHORD on a Tonnetz walk, each of the white keys C E G plays a note of the walk's triad.
Why it matters: the first three white keys can only sound chord tones. -/
theorem keys_triad_is_the_chord (t key : UInt32) (triad : t < 24) (k12 : key < 12) :
    ∀ w : Fin 3, (Harmony.rotate (Tonnetz.mask t.toNat) key.toNat).testBit
      ((key.toNat + Keys.degree (Harmony.rotate (Tonnetz.mask t.toNat) key.toNat) key.toNat w.val) % 12) =
        true := by
  intro w
  exact keys_degree_in_mask _ _ _ (by rw [keys_triad_three t key triad k12]; decide)

/-- With CHORD on a Tonnetz walk, the pitch classes of white keys C E G together are exactly the walk's triad,
in rising order from the key's root (so degree 0 is the triad's root only when the walk is on the tonic).
Why it matters: the first three white keys are the whole chord and nothing else, laid out low to high. -/
theorem keys_triad_white_keys_are_the_chord (t key : UInt32) (triad : t < 24) (k12 : key < 12) :
    let mask := Harmony.rotate (Tonnetz.mask t.toNat) key.toNat
    (1 <<< ((key.toNat + Keys.degree mask key.toNat 0) % 12)) |||
      (1 <<< ((key.toNat + Keys.degree mask key.toNat 1) % 12)) |||
      (1 <<< ((key.toNat + Keys.degree mask key.toNat 2) % 12)) = mask :=
  keys_triad_degrees_make_mask ⟨t.toNat, UInt32.lt_iff_toNat_lt.mp triad⟩
    ⟨key.toNat, UInt32.lt_iff_toNat_lt.mp k12⟩
