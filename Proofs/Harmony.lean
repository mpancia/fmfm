import Spec.Harmony

/-- The C entries reduce their arguments as 32-bit numbers; as plain numbers that is the same reduction. -/
private theorem harmony_mod_toNat (x : UInt32) (n : UInt32) : (x % n).toNat = x.toNat % n.toNat := UInt32.toNat_mod x n

/-- Checked for every scale, key, chord root and follow mode: the mask is never empty and fits in 12 bits. -/
private theorem harmony_every_mask_ok :
    ∀ scale, scale < 14 → ∀ key, key < 12 → ∀ root, root < 12 → ∀ follow, follow < 4 →
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
  simp only [harmony_mod_toNat, show (14 : UInt32).toNat = 14 from rfl, show (12 : UInt32).toNat = 12 from rfl,
    show (8 : UInt32).toNat = 8 from rfl, show (4 : UInt32).toNat = 4 from rfl]
  have ⟨ne, small⟩ := harmony_every_mask_ok (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) (root.toNat % 12) (Nat.mod_lt _ (by decide)) (follow.toNat % 4)
    (Nat.mod_lt _ (by decide))
  generalize Harmony.laneMask (scale.toNat % 14) (key.toNat % 12) (root.toNat % 12) (follow.toNat % 4) = m
    at *
  simp [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show m < 2 ^ 32 by omega), ne, small]

/-- With chord follow, 7TH or TRIAD, every note a lane may play is a note of the key's scale, whatever chord
it is on: the chord is stacked from the key's scale at the chord root, not a shape moved to the root.
Why it matters: a chord progression played with chord follow stays in the key. (The ii chord of C major is
D F A, not D F# A; the second is what a transposed shape gave, and trying to prove this is what caught it.) -/
theorem harmony_follow_in_key (scale key root follow : UInt32) (chordal : follow.toNat % 4 < 3) :
    (harmonyMask scale key root follow).toNat &&& (harmonyMask scale key 0 0).toNat =
      (harmonyMask scale key root follow).toNat := by
  unfold harmonyMask
  simp only [harmony_mod_toNat, show (14 : UInt32).toNat = 14 from rfl, show (12 : UInt32).toNat = 12 from rfl,
    show (8 : UInt32).toNat = 8 from rfl, show (4 : UInt32).toNat = 4 from rfl]
  have ⟨_, s2⟩ := harmony_every_mask_ok (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) (root.toNat % 12) (Nat.mod_lt _ (by decide)) (follow.toNat % 4)
    (Nat.mod_lt _ (by decide))
  have ⟨_, s0⟩ := harmony_every_mask_ok (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) 0 (by decide) 0 (by decide)
  have inside := harmony_every_chord_in_key (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) (root.toNat % 12) (Nat.mod_lt _ (by decide)) (follow.toNat % 4) chordal
  simp only [show (0 : UInt32).toNat % 4 = 0 from rfl, show (0 : UInt32).toNat % 12 = 0 from rfl]
  generalize Harmony.laneMask (scale.toNat % 14) (key.toNat % 12) (root.toNat % 12) (follow.toNat % 4) = a at *
  generalize Harmony.laneMask (scale.toNat % 14) (key.toNat % 12) 0 0 = b at *
  simp [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega), inside]

/-- With chord follow on a chord of a progression, the chord's root is among the lane's notes, in every scale
and key (and without follow it is too, being a note of the key).
Why it matters: joined with `harmony_chord_root_in_key`, a progression's chord is a chord of the key with its
root present; a lane following it can play the root, not only upper notes of some other chord. -/
theorem harmony_progression_chord_has_root (scale key progression step follow : UInt32)
    (chordal : follow.toNat % 4 < 3) :
    (harmonyMask scale key (harmonyChordRoot scale progression step) follow).toNat.testBit
      ((key.toNat % 12 + (harmonyChordRoot scale progression step).toNat) % 12) = true := by
  unfold harmonyMask harmonyChordRoot
  simp only [harmony_mod_toNat, show (14 : UInt32).toNat = 14 from rfl, show (12 : UInt32).toNat = 12 from rfl,
    show (8 : UInt32).toNat = 8 from rfl, show (4 : UInt32).toNat = 4 from rfl]
  have ⟨_, small⟩ := harmony_every_root_in_scale (scale.toNat % 14) (Nat.mod_lt _ (by decide))
    (progression.toNat % 8) (Nat.mod_lt _ (by decide)) (step.toNat % 4) (Nat.mod_lt _ (by decide))
  have has := harmony_every_chord_has_root (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) (progression.toNat % 8) (Nat.mod_lt _ (by decide)) (step.toNat % 4)
    (Nat.mod_lt _ (by decide)) (follow.toNat % 4) chordal
  have ⟨_, s2⟩ := harmony_every_mask_ok (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) (Harmony.chordRoot (scale.toNat % 14) (progression.toNat % 8) (step.toNat % 4))
    small (follow.toNat % 4) (Nat.mod_lt _ (by decide))
  generalize Harmony.chordRoot (scale.toNat % 14) (progression.toNat % 8) (step.toNat % 4) = r at *
  have rn : (r.toUInt32).toNat = r := by
    simp [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show r < 2 ^ 32 by omega)]
  simp only [rn, Nat.mod_eq_of_lt small]
  generalize Harmony.laneMask (scale.toNat % 14) (key.toNat % 12) r (follow.toNat % 4) = a at *
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
  simp only [harmony_mod_toNat, show (14 : UInt32).toNat = 14 from rfl, show (12 : UInt32).toNat = 12 from rfl,
    show (8 : UInt32).toNat = 8 from rfl, show (4 : UInt32).toNat = 4 from rfl]
  have ⟨inScale, small⟩ := harmony_every_root_in_scale (scale.toNat % 14) (Nat.mod_lt _ (by decide))
    (progression.toNat % 8) (Nat.mod_lt _ (by decide)) (step.toNat % 4) (Nat.mod_lt _ (by decide))
  generalize Harmony.chordRoot (scale.toNat % 14) (progression.toNat % 8) (step.toNat % 4) = r at *
  simp [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show r < 2 ^ 32 by omega), inScale, small]

/-- Splitting a count by a second test: the ones that pass it and the ones that do not add up. -/
private theorem harmony_count_split (p q : Nat → Bool) : ∀ l : List Nat,
    (l.filter (fun k => p k && q k)).length + (l.filter (fun k => p k && !q k)).length = (l.filter p).length := by
  intro l
  induction l with
  | nil => rfl
  | cons k rest ih =>
    simp only [List.filter_cons]
    cases p k <;> cases q k <;> simp <;> omega

/-- Turning the cycle by one: the same points are counted. -/
private theorem harmony_count_turn_one (n : Nat) (positive : 0 < n) (f : Nat → Bool) :
    ((List.range n).filter (fun k => f ((k + 1) % n))).length = ((List.range n).filter f).length := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have inner : (List.range m).filter (fun k => f ((k + 1) % (m + 1))) =
      (List.range m).filter (fun k => f (k + 1)) := by
    apply List.filter_congr
    intro k mem
    rw [Nat.mod_eq_of_lt (by have := List.mem_range.mp mem; omega)]
  have left : ((List.range (m + 1)).filter (fun k => f ((k + 1) % (m + 1)))).length =
      ((List.range m).filter (fun k => f (k + 1))).length + (if f 0 then 1 else 0) := by
    rw [List.range_succ, List.filter_append, List.length_append, inner]
    simp only [List.filter_cons, List.filter_nil, Nat.mod_self]
    cases f 0 <;> simp
  have right : ((List.range (m + 1)).filter f).length =
      (if f 0 then 1 else 0) + ((List.range m).filter (fun k => f (k + 1))).length := by
    rw [List.range_succ_eq_map, List.filter_cons, List.filter_map]
    cases f 0 <;> simp [Function.comp_def] <;> omega
  rw [left, right]
  omega

/-- Turning the cycle by any amount: the same points are counted. -/
private theorem harmony_count_turn (n : Nat) (positive : 0 < n) (f : Nat → Bool) : ∀ d,
    ((List.range n).filter (fun k => f ((k + d) % n))).length = ((List.range n).filter f).length := by
  intro d
  induction d with
  | zero =>
    apply congrArg List.length
    apply List.filter_congr
    intro k mem
    rw [Nat.add_zero, Nat.mod_eq_of_lt (List.mem_range.mp mem)]
  | succ d ih =>
    have turned := harmony_count_turn_one n positive (fun k => f ((k + d) % n))
    rw [← ih, ← turned]
    apply congrArg List.length
    apply List.filter_congr
    intro k _
    rw [Nat.mod_add_mod, show k + 1 + d = k + (d + 1) by omega]

/-- Babbitt's hexachord theorem in its general form, any cycle `Z_n` and any set: the pairs at distance `d` in
the complement are the pairs at that distance in the set, plus `n - 2 * size` (an ordered count, each
unordered pair seen from both ends). With `size = n / 2`, a hexachord in `Z_12`, the two are equal: a
six-note set and the six notes it leaves out have the same interval content.
Why it matters: it is why COMPL sounds like the scale it was cut from: the black keys have the white keys'
intervals, two fewer of each, and the whole-tone scale's complement has exactly its own. The theorem is the
reason Babbitt could build twelve-tone rows from a hexachord and its complement and have both halves sound
alike; here it is proved for every `n` and every set, by counting, with the twelve-note instance checked
note by note as `harmony_hexachord_theorem`. -/
theorem harmony_complement_interval_content (n d : Nat) (positive : 0 < n) (S : Nat → Bool) :
    Harmony.pairs n d (fun k => !S k) + 2 * Harmony.count n S = Harmony.pairs n d S + n := by
  unfold Harmony.pairs Harmony.count
  -- the four kinds of point: in and in, in and out, out and in, out and out
  have inSplit := harmony_count_split S (fun k => S ((k + d) % n)) (List.range n)
  have outSplit := harmony_count_split (fun k => !S k) (fun k => S ((k + d) % n)) (List.range n)
  have aheadSplit := harmony_count_split (fun k => S ((k + d) % n)) S (List.range n)
  have ahead := harmony_count_turn n positive S d
  have total : ((List.range n).filter S).length + ((List.range n).filter (fun k => !S k)).length = n := by
    have := harmony_count_split (fun _ => true) S (List.range n)
    simp only [Bool.true_and, List.filter_eq_self.mpr (fun _ _ => rfl), List.length_range] at this
    exact this
  have swap : ((List.range n).filter (fun k => S ((k + d) % n) && S k)).length =
      ((List.range n).filter (fun k => S k && S ((k + d) % n))).length := by
    apply congrArg List.length; apply List.filter_congr; intro k _; rw [Bool.and_comm]
  have swap2 : ((List.range n).filter (fun k => S ((k + d) % n) && !S k)).length =
      ((List.range n).filter (fun k => !S k && S ((k + d) % n))).length := by
    apply congrArg List.length; apply List.filter_congr; intro k _; rw [Bool.and_comm]
  rw [swap, swap2] at aheadSplit
  show (List.filter (fun k => !S k && !S ((k + d) % n)) (List.range n)).length + 2 * _ = _
  omega

/-- Babbitt's hexachord theorem on the firmware's own masks: every six-note set of the twelve pitch classes has
the interval vector of the six it leaves out, checked for all 4096 masks.
Why it matters: the instance the name comes from, on the 12-bit masks the lanes play from: a hexachord and its
complement are indistinguishable by interval content, which is the general theorem above at `n = 12`,
`size = 6`, where the difference `n - 2 * size` is zero. -/
theorem harmony_hexachord_theorem (mask : Nat) (small : mask < 4096) (six : Harmony.size mask = 6) :
    Harmony.intervalVector mask = Harmony.intervalVector (0xFFF ^^^ mask) := by
  have checked : ∀ high : Fin 64, ∀ low : Fin 64, Harmony.size (high.val * 64 + low.val) = 6 →
      Harmony.intervalVector (high.val * 64 + low.val) =
        Harmony.intervalVector (0xFFF ^^^ (high.val * 64 + low.val)) := by
    decide +kernel
  have split : mask = mask / 64 * 64 + mask % 64 := by omega
  have := checked ⟨mask / 64, by omega⟩ ⟨mask % 64, by omega⟩
  rw [split]
  exact this (split ▸ six)

/-- Checked for every scale and key: COMPL plays exactly the notes outside the key's scale, except for the
chromatic scale, which it leaves whole. -/
private theorem harmony_every_complement_outside :
    ∀ scale, scale < 14 → ∀ key, key < 12 → ∀ root, root < 12 →
      let inKey := Harmony.laneMask scale key 0 0
      (inKey = 0xFFF ∧ Harmony.laneMask scale key root 3 = 0xFFF) ∨
        (Harmony.laneMask scale key root 3 &&& inKey = 0 ∧
          Harmony.laneMask scale key root 3 ||| inKey = 0xFFF) := by
  decide +kernel

/-- COMPL (chord follow 3) plays the notes outside the key's scale and nothing else, for every scale and key,
whatever chord is on; the chromatic scale, which leaves nothing out, plays whole.
Why it matters: COMPL is a second voice that never collides with a lane in the key, the black keys to its
white; with `harmony_complement_interval_content` it has the key's intervals, so it belongs to the same music
while sharing no note with it. -/
theorem harmony_complement_outside_key (scale key root follow : UInt32) (compl : follow.toNat % 4 = 3) :
    let inKey := (harmonyMask scale key 0 0).toNat
    let outside := (harmonyMask scale key root follow).toNat
    (inKey = 0xFFF ∧ outside = 0xFFF) ∨ (outside &&& inKey = 0 ∧ outside ||| inKey = 0xFFF) := by
  intro inKey outside
  have ⟨_, s0⟩ := harmony_every_mask_ok (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) 0 (by decide) 0 (by decide)
  have ⟨_, s3⟩ := harmony_every_mask_ok (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) (root.toNat % 12) (Nat.mod_lt _ (by decide)) 3 (by decide)
  have := harmony_every_complement_outside (scale.toNat % 14) (Nat.mod_lt _ (by decide)) (key.toNat % 12)
    (Nat.mod_lt _ (by decide)) (root.toNat % 12) (Nat.mod_lt _ (by decide))
  simp only [inKey, outside, harmonyMask, harmony_mod_toNat, show (14 : UInt32).toNat = 14 from rfl,
    show (12 : UInt32).toNat = 12 from rfl, show (4 : UInt32).toNat = 4 from rfl, compl,
    show (0 : UInt32).toNat % 4 = 0 from rfl, show (0 : UInt32).toNat % 12 = 0 from rfl]
  generalize Harmony.laneMask (scale.toNat % 14) (key.toNat % 12) (root.toNat % 12) 3 = a at *
  generalize Harmony.laneMask (scale.toNat % 14) (key.toNat % 12) 0 0 = b at *
  simp only [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega)]
  exact this
