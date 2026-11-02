import Spec.Harmony

/-- The C entries reduce their arguments as 32-bit numbers; as plain numbers that is the same reduction. -/
private theorem harmony_mod_toNat (x : UInt32) (n : UInt32) : (x % n).toNat = x.toNat % n.toNat :=
  UInt32.toNat_mod x n

/-- A made triad is below 24. -/
private theorem tonnetz_make_lt (r : Nat) (m : Bool) : Tonnetz.make r m < 24 := by
  unfold Tonnetz.make; cases m <;> simp <;> omega

/-- A move lands below 24. -/
private theorem tonnetz_step_lt (g t : Nat) : Tonnetz.step g t < 24 := by
  unfold Tonnetz.step Tonnetz.P Tonnetz.L Tonnetz.R
  split <;> (try split) <;> exact tonnetz_make_lt _ _

/-- A walk only ever stands on one of the 24 triads. -/
private theorem tonnetz_walk_lt (word start : Nat) : ∀ count, Tonnetz.walk word start count < 24 := by
  intro count
  cases count with
  | zero => exact Nat.mod_lt _ (by decide)
  | succ count => exact tonnetz_step_lt _ _

/-- A word's letters are 0, 1 or 2. -/
private theorem tonnetz_letter_lt (word i : Nat) : Tonnetz.letter word i < 3 := by
  unfold Tonnetz.letter; split <;> omega

/-- A walk's chord is one of the 24 triads. -/
private theorem harmony_walk_chord_lt (scale p s : Nat) : Harmony.walkChord scale p s < 24 :=
  tonnetz_walk_lt _ _ _

/-- A table progression repeats every four chords: the mask and the root only see the chord count modulo 4. -/
private theorem harmony_table_period (scale key p s follow : Nat) (table : p < 8) :
    Harmony.laneMask scale key p s follow = Harmony.laneMask scale key p (s % 4) follow ∧
      Harmony.chordRoot scale p s = Harmony.chordRoot scale p (s % 4) := by
  have w : Harmony.walks p = false := by unfold Harmony.walks; simp; omega
  constructor
  · unfold Harmony.laneMask Harmony.chordRoot Harmony.degree
    simp only [Nat.mod_mod, w, Bool.false_eq_true, ite_false]
  · unfold Harmony.chordRoot Harmony.degree
    simp only [Nat.mod_mod]

/-- Checked for every scale, key, table progression, chord and follow mode: the mask is never empty and fits
in 12 bits. -/
private theorem harmony_every_table_mask_ok :
    ∀ scale : Fin 14, ∀ key : Fin 12, ∀ p : Fin 8, ∀ s : Fin 4, ∀ follow : Fin 4,
      Harmony.laneMask scale key p s follow ≠ 0 ∧ Harmony.laneMask scale key p s follow < 4096 := by
  decide +kernel

/-- Checked likewise for OFF, 7TH and TRIAD: the mask is inside the key's scale and holds the chord root. -/
private theorem harmony_every_table_chord_ok :
    ∀ scale : Fin 14, ∀ key : Fin 12, ∀ p : Fin 8, ∀ s : Fin 4, ∀ follow : Fin 3,
      Harmony.laneMask scale key p s follow &&& Harmony.laneMask scale key 0 0 0 =
          Harmony.laneMask scale key p s follow ∧
        (Harmony.laneMask scale key p s follow).testBit ((key + Harmony.chordRoot scale p s) % 12) =
            true := by
  decide +kernel

/-- Checked for every triad and key: a walk's triad turned to the key is three notes in 12 bits with its root
among them. -/
private theorem harmony_every_walk_mask_ok :
    ∀ t : Fin 24, ∀ key : Fin 12,
      Harmony.rotate (Tonnetz.mask t) key ≠ 0 ∧ Harmony.rotate (Tonnetz.mask t) key < 4096 ∧
        Harmony.size (Harmony.rotate (Tonnetz.mask t) key) = 3 ∧
        (Harmony.rotate (Tonnetz.mask t) key).testBit ((key + Tonnetz.root t) % 12) = true := by
  decide +kernel

/-- Checked for every triad and move: the triad after a move shares exactly two notes with the one before. -/
private theorem tonnetz_every_move_keeps_two :
    ∀ t : Fin 24, ∀ g : Fin 3, Harmony.size (Tonnetz.mask t &&& Tonnetz.mask (Tonnetz.step g t)) = 2 := by
  decide +kernel

/-- Checked for every scale, table progression and chord: the root is a note of the scale and below an octave. -/
private theorem harmony_every_root_in_scale :
    ∀ scale : Fin 14, ∀ p : Fin 8, ∀ s : Fin 4,
      (Harmony.scale scale).testBit (Harmony.chordRoot scale p s) = true ∧
          Harmony.chordRoot scale p s < 12 := by
  decide +kernel

/-- On a walk, 7TH and TRIAD both give the walk's triad turned to the key. -/
private theorem harmony_walk_mask (scale key p s follow : Nat) (walk : 8 ≤ p) (chordal : 1 ≤ follow ∧
    follow ≤ 2) :
    Harmony.laneMask scale key p s follow =
        Harmony.rotate (Tonnetz.mask (Harmony.walkChord scale p s)) (key % 12) := by
  unfold Harmony.laneMask
  have w : Harmony.walks p = true := by unfold Harmony.walks; simp [walk]
  simp only [show follow ≠ 3 by omega, show follow ≠ 0 by omega, w, ite_true, ite_false]

/-- OFF and COMPL see only the key's scale, whatever the progression and chord. -/
private theorem harmony_key_only (scale key p s follow : Nat) (plain : follow = 0 ∨ follow = 3) :
    Harmony.laneMask scale key p s follow = Harmony.laneMask scale key 0 0 follow := by
  unfold Harmony.laneMask
  rcases plain with rfl | rfl <;> simp

/-- The mask, for any settings in range: never empty, 12 bits. -/
private theorem harmony_mask_ok (scale key p s follow : Nat) (sc : scale < 14) (k : key < 12) (pr : p < 11)
    (st : s < 24) (f : follow < 4) :
    Harmony.laneMask scale key p s follow ≠ 0 ∧ Harmony.laneMask scale key p s follow < 4096 := by
  rcases Nat.lt_or_ge p 8 with table | walk
  · rw [(harmony_table_period scale key p s follow table).1]
    exact harmony_every_table_mask_ok ⟨scale, sc⟩ ⟨key, k⟩ ⟨p, table⟩ ⟨s % 4,
        Nat.mod_lt _ (by decide)⟩ ⟨follow, f⟩
  · by_cases plain : follow = 0 ∨ follow = 3
    · rw [harmony_key_only scale key p s follow plain]
      exact harmony_every_table_mask_ok ⟨scale, sc⟩ ⟨key, k⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨follow, f⟩
    · rw [harmony_walk_mask scale key p s follow walk (by omega), Nat.mod_eq_of_lt k]
      have ⟨ne, small, _⟩ := harmony_every_walk_mask_ok ⟨Harmony.walkChord scale p s,
          harmony_walk_chord_lt _ _ _⟩
        ⟨key, k⟩
      exact ⟨ne, small⟩

/-- The chord root, for any settings in range: below an octave. -/
private theorem harmony_root_lt (scale p s : Nat) (sc : scale < 14) (pr : p < 11) (st : s < 24) :
    Harmony.root scale p s < 12 := by
  unfold Harmony.root
  rcases Nat.lt_or_ge p 8 with table | walk
  · have w : Harmony.walks p = false := by unfold Harmony.walks; simp; omega
    simp only [w, Bool.false_eq_true, ite_false]
    rw [(harmony_table_period scale 0 p s 0 table).2]
    exact (harmony_every_root_in_scale ⟨scale, sc⟩ ⟨p, table⟩ ⟨s % 4, Nat.mod_lt _ (by decide)⟩).2
  · have w : Harmony.walks p = true := by unfold Harmony.walks; simp [walk]
    simp only [w, ite_true]
    exact Nat.mod_lt _ (by decide)

/-- The settings as the C entries reduce them. -/
private theorem harmony_args (scale key progression step follow : UInt32) :
    (harmonyMask scale key progression step follow).toNat =
        Harmony.laneMask (scale.toNat % 14) (key.toNat % 12)
      (progression.toNat % 11) (step.toNat % 24) (follow.toNat % 4) ∧
    (harmonyChordRoot scale progression step).toNat =
      Harmony.root (scale.toNat % 14) (progression.toNat % 11) (step.toNat % 24) := by
  unfold harmonyMask harmonyChordRoot
  simp only [harmony_mod_toNat, show (14 : UInt32).toNat = 14 from rfl, show (12 : UInt32).toNat =
      12 from rfl,
    show (11 : UInt32).toNat = 11 from rfl, show (24 : UInt32).toNat = 24 from rfl,
    show (4 : UInt32).toNat = 4 from rfl]
  have ⟨_, small⟩ := harmony_mask_ok (scale.toNat % 14) (key.toNat % 12) (progression.toNat % 11)
    (step.toNat % 24) (follow.toNat % 4) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  have root := harmony_root_lt (scale.toNat % 14) (progression.toNat % 11) (step.toNat % 24)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  generalize Harmony.laneMask (scale.toNat % 14) (key.toNat % 12) (progression.toNat % 11) (step.toNat % 24)
    (follow.toNat % 4) = a at *
  generalize Harmony.root (scale.toNat % 14) (progression.toNat % 11) (step.toNat % 24) = r at *
  simp [Nat.toUInt32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show r < 2 ^ 32 by omega)]

/-- The mask handed to a lane is non-empty and fits in 12 bits, for every scale, key, progression, chord step
and follow mode, Tonnetz walks included.
Why it matters: `lane_note_in_scale` needs a non-empty 12-bit mask; a chord change can never leave a lane
with nothing to play. -/
theorem harmony_mask_never_empty (scale key progression step follow : UInt32) :
    (harmonyMask scale key progression step follow).toNat ≠ 0 ∧
      (harmonyMask scale key progression step follow).toNat < 4096 := by
  rw [(harmony_args scale key progression step follow).1]
  exact harmony_mask_ok _ _ _ _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))

/-- On a table progression with chord follow 7TH or TRIAD, every note a lane may play is in the key's scale:
the chord is stacked from the key's scale at the chord root, not a transposed shape. (The ii chord of C major
is D F A, not D F# A.) Tonnetz walks are excluded on purpose; see `harmony_walk_chord_is_triad`.
Why it matters: chord follow on a table progression stays in key. -/
theorem harmony_follow_in_key (scale key progression step follow : UInt32)
    (table : progression.toNat % 11 < 8) (chordal : follow.toNat % 4 < 3) :
    (harmonyMask scale key progression step follow).toNat &&& (harmonyMask scale key 0 0 0).toNat =
      (harmonyMask scale key progression step follow).toNat := by
  rw [(harmony_args scale key progression step follow).1, (harmony_args scale key 0 0 0).1]
  simp only [show (0 : UInt32).toNat % 11 = 0 from rfl, show (0 : UInt32).toNat % 24 = 0 from rfl,
    show (0 : UInt32).toNat % 4 = 0 from rfl]
  rw [(harmony_table_period _ _ _ _ _ table).1]
  exact (harmony_every_table_chord_ok ⟨_, Nat.mod_lt _ (by decide)⟩ ⟨_, Nat.mod_lt _ (by decide)⟩ ⟨_, table⟩
    ⟨_, Nat.mod_lt _ (by decide)⟩ ⟨_, chordal⟩).1

/-- With chord follow 7TH or TRIAD the chord's root is among the lane's notes, for every scale and key, on
tables and walks alike.
Why it matters: a following lane can play the root, not only upper notes of the chord. -/
theorem harmony_progression_chord_has_root (scale key progression step follow : UInt32)
    (chordal : 1 ≤ follow.toNat % 4 ∧ follow.toNat % 4 ≤ 2) :
    (harmonyMask scale key progression step follow).toNat.testBit
      ((key.toNat % 12 + (harmonyChordRoot scale progression step).toNat) % 12) = true := by
  rw [(harmony_args scale key progression step follow).1, (harmony_args scale key progression step follow).2]
  unfold Harmony.root
  rcases Nat.lt_or_ge (progression.toNat % 11) 8 with table | walk
  · have w : Harmony.walks (progression.toNat % 11) = false := by unfold Harmony.walks; simp; omega
    simp only [w, Bool.false_eq_true, ite_false]
    rw [(harmony_table_period _ _ _ _ _ table).1, (harmony_table_period (scale.toNat % 14) 0 _ _ 0 table).2]
    exact (harmony_every_table_chord_ok ⟨_, Nat.mod_lt _ (by decide)⟩ ⟨_, Nat.mod_lt _ (by decide)⟩ ⟨_, table⟩
      ⟨_, Nat.mod_lt _ (by decide)⟩ ⟨_, by omega⟩).2
  · have w : Harmony.walks (progression.toNat % 11) = true := by unfold Harmony.walks; simp [walk]
    simp only [w, ite_true]
    rw [harmony_walk_mask _ _ _ _ _ walk chordal, Nat.mod_mod]
    exact (harmony_every_walk_mask_ok ⟨_, harmony_walk_chord_lt _ _ _⟩ ⟨_, Nat.mod_lt _ (by decide)⟩).2.2.2

/-- On a table progression every chord root is a note of the key's scale (below an octave).
Why it matters: progressions are written as degrees, so 1-4-5-1 is I IV V in major and i iv v in minor; a
table chord never lands outside the key. A walk's root can. -/
theorem harmony_chord_root_in_key (scale progression step : UInt32) (table : progression.toNat % 11 < 8) :
    (Harmony.scale (scale.toNat % 14)).testBit (harmonyChordRoot scale progression step).toNat = true ∧
      (harmonyChordRoot scale progression step).toNat < 12 := by
  rw [(harmony_args scale 0 progression step 0).2]
  unfold Harmony.root
  have w : Harmony.walks (progression.toNat % 11) = false := by unfold Harmony.walks; simp; omega
  simp only [w, Bool.false_eq_true, ite_false]
  rw [(harmony_table_period (scale.toNat % 14) 0 _ _ 0 table).2]
  exact harmony_every_root_in_scale ⟨_, Nat.mod_lt _ (by decide)⟩ ⟨_, table⟩ ⟨_, Nat.mod_lt _ (by decide)⟩

/-- On a Tonnetz walk (progressions 8 and up) with chord follow 7TH or TRIAD, a lane plays exactly the walk's
triad transposed to the key: three notes, the chord the screen names.
Why it matters: walks leave the key on purpose, and the lane plays exactly the named triad. -/
theorem harmony_walk_chord_is_triad (scale key progression step follow : UInt32)
    (walk : 8 ≤ progression.toNat % 11) (chordal : 1 ≤ follow.toNat % 4 ∧ follow.toNat % 4 ≤ 2) :
    (harmonyMask scale key progression step follow).toNat = Harmony.rotate
      (Tonnetz.mask (Harmony.walkChord (scale.toNat % 14) (progression.toNat % 11) (step.toNat % 24)))
      (key.toNat % 12) ∧
    Harmony.size (harmonyMask scale key progression step follow).toNat = 3 := by
  rw [(harmony_args scale key progression step follow).1, harmony_walk_mask _ _ _ _ _ walk chordal,
      Nat.mod_mod]
  exact ⟨rfl, (harmony_every_walk_mask_ok ⟨_, harmony_walk_chord_lt _ _ _⟩ ⟨_,
      Nat.mod_lt _ (by decide)⟩).2.2.1⟩

/-- Consecutive chords of any Tonnetz walk share exactly two pitch classes.
Why it matters: P, L and R each change one note of a triad, so a walk moves one note at a time. -/
theorem harmony_walk_keeps_two_notes (word start count : Nat) :
    Harmony.size (Tonnetz.mask (Tonnetz.walk word start count) &&&
      Tonnetz.mask (Tonnetz.walk word start (count + 1))) = 2 := by
  show Harmony.size (Tonnetz.mask (Tonnetz.walk word start count) &&&
    Tonnetz.mask (Tonnetz.step (Tonnetz.letter word count) (Tonnetz.walk word start count))) = 2
  exact tonnetz_every_move_keeps_two ⟨_, tonnetz_walk_lt _ _ _⟩ ⟨_, tonnetz_letter_lt _ _⟩

/-- Checked for every scale and key: COMPL plays exactly the notes outside the key's scale, except for the
chromatic scale, which it leaves whole. -/
private theorem harmony_every_complement_outside :
    ∀ scale : Fin 14, ∀ key : Fin 12,
      let inKey := Harmony.laneMask scale key 0 0 0
      (inKey = 0xFFF ∧ Harmony.laneMask scale key 0 0 3 = 0xFFF) ∨
        (Harmony.laneMask scale key 0 0 3 &&& inKey = 0 ∧ Harmony.laneMask scale key 0 0 3 ||| inKey =
            0xFFF) := by
  decide +kernel

/-- COMPL (chord follow 3) plays exactly the notes outside the key's scale, for every scale, key and chord;
the chromatic scale plays whole.
Why it matters: a COMPL lane never shares a note with a lane in the key. -/
theorem harmony_complement_outside_key (scale key progression step follow : UInt32)
    (compl : follow.toNat % 4 = 3) :
    let inKey := (harmonyMask scale key 0 0 0).toNat
    let outside := (harmonyMask scale key progression step follow).toNat
    (inKey = 0xFFF ∧ outside = 0xFFF) ∨ (outside &&& inKey = 0 ∧ outside ||| inKey = 0xFFF) := by
  intro inKey outside
  have a := (harmony_args scale key progression step follow).1
  have b := (harmony_args scale key 0 0 0).1
  simp only [show (0 : UInt32).toNat % 11 = 0 from rfl, show (0 : UInt32).toNat % 24 = 0 from rfl,
    show (0 : UInt32).toNat % 4 = 0 from rfl] at b
  rw [compl, harmony_key_only _ _ _ _ 3 (Or.inr rfl)] at a
  simp only [inKey, outside, a, b]
  exact harmony_every_complement_outside ⟨_, Nat.mod_lt _ (by decide)⟩ ⟨_, Nat.mod_lt _ (by decide)⟩

/-- Splitting a count by a second test: the ones that pass it and the ones that do not add up. -/
private theorem harmony_count_split (p q : Nat → Bool) : ∀ l : List Nat,
    (l.filter (fun k => p k && q k)).length + (l.filter (fun k => p k && !q k)).length =
        (l.filter p).length := by
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

/-- Babbitt's hexachord theorem for any cycle `Z_n` and any set: the ordered count of pairs at distance `d` in
the complement equals the count in the set plus `n - 2 * size`. For `size = n / 2` the two are equal.
Why it matters: a hexachord and its complement have the same interval content, which is why COMPL sounds like
the scale it was cut from. -/
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

/-- Babbitt's hexachord theorem on the 12-bit masks: every six-note mask has the interval vector of its
complement, checked for all 4096 masks.
Why it matters: the `n = 12`, `size = 6` instance of `harmony_complement_interval_content` on the masks the
lanes play from. -/
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

