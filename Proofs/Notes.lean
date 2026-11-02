import Spec.Notes
import Firmware.Quantizer
import Proofs.Random

/-- Every list `Notes.fill` makes has its full length and only positions inside the range. -/
private theorem notes_fill_shape (span : Nat) (positive : 0 < span) (small : span ≤ 65535) :
    ∀ count seed, (Notes.fill span count seed).length = count ∧
      ∀ x ∈ Notes.fill span count seed, x < span := by
  intro count
  induction count with
  | zero => intro seed; simp [Notes.fill]
  | succ count ih =>
    intro seed
    have first : (Random.below seed span.toUInt32).toNat < span := by
      have spanSmall : span.toUInt32.toNat = span := by simp; omega
      have := random_below_lt seed span.toUInt32 (by rw [spanSmall]; exact positive)
        (by rw [spanSmall]; exact small)
      rwa [spanSmall] at this
    obtain ⟨len, below⟩ := ih (Random.next seed)
    refine ⟨by simp [Notes.fill, len], ?_⟩
    intro x mem
    simp only [Notes.fill, List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact first
    · exact below x mem

/-- A fresh note memory is valid for any span from 1 to 65535 and any loop length from 1 to 16.
Why it matters: the lane starts in a state the algorithms can rely on, whatever the seed. -/
theorem notes_start_valid (span amount : Nat) (seed : UInt32) (positive : 0 < span) (small : span ≤ 65535)
    (loopLength : 0 < amount) : NoteState.Valid span amount (Notes.start span seed) := by
  obtain ⟨len, below⟩ := notes_fill_shape span positive small Notes.regLen seed
  exact ⟨by simp [Notes.start]; omega, by simp [Notes.start]; omega, by simpa [Notes.start] using len,
    by simpa [Notes.start] using below⟩

/-- Setting one slot of a consistent loop memory to a position inside the range keeps it consistent. -/
private theorem notes_set_keeps_memory (span : Nat) (s : NoteState) (valid : s.reg.length = Notes.regLen)
    (below : ∀ x ∈ s.reg, x < span) (slot value : Nat) (inside : value < span) :
    (s.reg.set slot value).length = Notes.regLen ∧ ∀ x ∈ s.reg.set slot value, x < span := by
  refine ⟨by simpa using valid, ?_⟩
  intro x mem
  rcases List.mem_or_eq_of_mem_set mem with old | rfl
  · exact below x old
  · exact inside

/-- Whichever algorithm picks, the offset is below `span` and the memory stays valid.
Why it matters: no algorithm can pick outside the range or corrupt the memory the next pick depends on. -/
theorem notes_choose_stays_in_range (rule : NoteRule) (span mask low : Nat) (s : NoteState) (any step chance : Nat)
    (positive : 0 < span) (loopLength : 0 < rule.amount) (fits : rule.amount ≤ Notes.regLen)
    (valid : NoteState.Valid span rule.amount s) (anyBelow : any < span) :
    (Notes.choose rule span mask low s any step chance).offset < span ∧
      NoteState.Valid span rule.amount (Notes.choose rule span mask low s any step chance).state := by
  obtain ⟨pos, slot, full, below⟩ := valid
  have replayOk : (Notes.replay rule span s any chance).offset < span ∧
      NoteState.Valid span rule.amount (Notes.replay rule span s any chance).state := by
    have inRange : s.slot < s.reg.length := by omega
    have kept : s.reg.getD s.slot 0 < span := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inRange, Option.getD_some]
      exact below _ (List.getElem_mem inRange)
    have value : (if chance < rule.mutate then any else s.reg.getD s.slot 0) < span := by split <;> assumption
    obtain ⟨len, mem⟩ := notes_set_keeps_memory span s full below s.slot _ value
    exact ⟨value, pos, Nat.mod_lt _ loopLength, len, mem⟩
  have moveOk : ∀ p m, p < span → Notes.moveBy span p m < span := by
    intro p m h; unfold Notes.moveBy; split <;> omega
  have turingBelow : ∀ b, (b % 256) * span / 256 < span := by
    intro b
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 256), Nat.mul_comm span 256]
    exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (by decide)) positive
  unfold Notes.choose
  split
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> (try split) <;> omega
  · exact ⟨Nat.mod_lt _ positive, Nat.mod_lt _ positive, slot, full, below⟩
  · exact ⟨Nat.mod_lt _ positive, Nat.mod_lt _ positive, slot, full, below⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> (try split) <;> (try split) <;> (try dsimp only) <;>
      first | omega | assumption | skip
  · exact replayOk
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> first | exact turingBelow _ | exact slot | exact full | exact below
  · exact replayOk
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> first | exact moveOk _ _ pos | exact slot | exact full | exact below
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> first | exact moveOk _ _ pos | exact slot | exact full | exact below
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> first | omega | exact Nat.mod_lt _ loopLength | exact full | exact below
  · exact ⟨anyBelow, anyBelow, slot, full, below⟩

/-- UP climbs one position a note and wraps: from position `p` the `i`-th note is at `(p + i) % span`, so the
first `span` notes visit every position once.
Why it matters: an UP lane covers its whole range with no position skipped or repeated. -/
theorem notes_up_visits_every_position (span p : Nat) (positive : 0 < span) (start : p < span) (s : NoteState)
    (atStart : s.pos = p) (n : Nat) :
    (Notes.picks ⟨2, 1, 0⟩ span n s).1 = (List.range n).map (fun i => (p + i + 1) % span) := by
  induction n generalizing s p with
  | zero => simp [Notes.picks]
  | succ n ih =>
    simp only [Notes.picks, Notes.choose, atStart, List.range_succ_eq_map, List.map_cons, List.map_map]
    rw [ih ((p + 1) % span) (Nat.mod_lt _ positive) _ rfl]
    simp only [List.cons.injEq, true_and]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp]
    rw [Nat.add_assoc ((p + 1) % span), Nat.mod_add_mod]
    congr 1; omega

/-- DOWN falls one position a note and wraps: from `p` the `i`-th note is at
`(p + (span - 1) * (i + 1)) % span`, so the first `span` notes visit every position once.
Why it matters: a DOWN lane covers its whole range with no position skipped or repeated. -/
theorem notes_down_visits_every_position (span p : Nat) (positive : 0 < span) (start : p < span)
    (s : NoteState)
    (atStart : s.pos = p) (n : Nat) :
    (Notes.picks ⟨3, 1, 0⟩ span n s).1 = (List.range n).map (fun i => (p + (span - 1) * (i + 1)) % span) := by
  induction n generalizing s p with
  | zero => simp [Notes.picks]
  | succ n ih =>
    simp only [Notes.picks, Notes.choose, atStart, List.range_succ_eq_map, List.map_cons, List.map_map]
    rw [ih ((p + span - 1) % span) (Nat.mod_lt _ positive) _ rfl]
    simp only [List.cons.injEq, Nat.zero_add]
    constructor
    · congr 1; omega
    · apply List.map_congr_left
      intro i _
      simp only [Function.comp]
      rw [Nat.mod_add_mod]
      congr 1
      have grow : (span - 1) * (i + 1 + 1) = (span - 1) * (i + 1) + (span - 1) := Nat.mul_succ _ _
      rw [grow]
      omega

/-- BOUNCE moves at most one position a note, for a span of at least 2.
Why it matters: a BOUNCE lane never leaps. -/
theorem notes_bounce_moves_one (span mask low : Nat) (s : NoteState) (wide : 2 ≤ span) (inside : s.pos < span)
    (any step chance : Nat) :
    (Notes.choose ⟨4, 1, 0⟩ span mask low s any step chance).offset + 1 = s.pos ∨
      (Notes.choose ⟨4, 1, 0⟩ span mask low s any step chance).offset = s.pos + 1 := by
  simp only [Notes.choose]
  split <;> (try split) <;> (try dsimp only) <;> omega

/-- WALK moves at most `amount` positions a note (the step is drawn below `2 * amount + 1`).
Why it matters: AMOUNT bounds how far a WALK lane can jump between notes. -/
theorem notes_walk_bounded (amount span mask low : Nat) (s : NoteState) (step any chance : Nat) (inside : s.pos < span)
    (drawn : step ≤ 2 * amount) :
    (Notes.choose ⟨1, amount, 0⟩ span mask low s any step chance).offset ≤ s.pos + amount ∧
      s.pos ≤ (Notes.choose ⟨1, amount, 0⟩ span mask low s any step chance).offset + amount := by
  simp only [Notes.choose]
  split <;> (try dsimp only) <;> omega

/-- LOOP with MUTATE at 0 repeats the same `amount` notes: the memory never changes and the slot wraps.
Why it matters: MUTATE 0 is an exact loop. -/
theorem notes_loop_repeats (amount span mask low : Nat) (s : NoteState)
    (fits : amount ≤ s.reg.length) (slot : s.slot < amount) (any step chance : Nat) :
    (Notes.choose ⟨5, amount, 0⟩ span mask low s any step chance).state.reg = s.reg ∧
      (Notes.choose ⟨5, amount, 0⟩ span mask low s any step chance).state.slot = (s.slot + 1) % amount ∧
      (Notes.choose ⟨5, amount, 0⟩ span mask low s any step chance).offset = s.reg.getD s.slot 0 := by
  have inRange : s.slot < s.reg.length := by omega
  simp only [Notes.choose, Notes.replay, Nat.not_lt_zero, ite_false, and_true]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inRange, Option.getD_some, List.set_getElem_self]

/-- A picked move is one of the seven classes. -/
private theorem notes_pick_move_bounded (weights : List Nat) (base pick : Nat) :
    Notes.pickMove weights base pick < Notes.moves := by
  unfold Notes.pickMove Notes.moves
  simp only
  omega

/-- MARKOV moves at most three positions a note, jump or not (move classes are -3 to +3; a doubled move is
clamped to that range).
Why it matters: a MARKOV lane never leaps, whatever it learnt from the keys or the style. -/
theorem notes_markov_moves_at_most_three (amount mutate span mask low : Nat) (s : NoteState)
    (any step chance : Nat) (inside : s.pos < span) :
    (Notes.choose ⟨8, amount, mutate⟩ span mask low s any step chance).offset ≤ s.pos + 3 ∧
      s.pos ≤ (Notes.choose ⟨8, amount, mutate⟩ span mask low s any step chance).offset + 3 := by
  simp only [Notes.choose]
  have bound := notes_pick_move_bounded (Notes.chainWeights (amount - 1) s.chain) (s.last % Notes.moves * Notes.moves)
    (if Notes.rowTotal (Notes.chainWeights (amount - 1) s.chain) (s.last % Notes.moves * Notes.moves) = 0 then 0
      else any * Notes.rowTotal (Notes.chainWeights (amount - 1) s.chain) (s.last % Notes.moves * Notes.moves) / span)
  generalize Notes.pickMove _ _ _ = move at *
  unfold Notes.moves at bound
  unfold Notes.moveBy
  split <;> split <;> (try split) <;> omega

/-- GRAMMAR moves at most two positions a note: its symbols step or skip, up or down.
Why it matters: a GRAMMAR lane never leaps, for any grammar and depth. -/
theorem notes_grammar_moves_at_most_two (amount mutate span mask low : Nat) (s : NoteState)
    (any step chance : Nat) (inside : s.pos < span) :
    (Notes.choose ⟨9, amount, mutate⟩ span mask low s any step chance).offset ≤ s.pos + 2 ∧
      s.pos ≤ (Notes.choose ⟨9, amount, mutate⟩ span mask low s any step chance).offset + 2 := by
  simp only [Notes.choose]
  generalize (Notes.phraseOf (amount - 1) (mutate / 25)).getD s.phrase 0 = sym
  unfold Notes.moveBy Notes.grammarMove
  split <;> split <;> omega

/-- `learn` (a key press) keeps the memory valid for any note: the step sequencer stores it in range, the
markov chain counts it.
Why it matters: nothing played on the keys can corrupt the memory. -/
theorem notes_learn_keeps_valid (rule : NoteRule) (span : Nat) (s : NoteState) (offset : Nat)
    (positive : 0 < span) (valid : NoteState.Valid span rule.amount s) :
    NoteState.Valid span rule.amount (Notes.learn rule span s offset) := by
  obtain ⟨pos, slot, full, below⟩ := valid
  unfold Notes.learn
  have cut : min (span - 1) offset < span := by omega
  split
  · obtain ⟨len, mem⟩ := notes_set_keeps_memory span s full below s.cursor _ cut
    exact ⟨cut, slot, len, mem⟩
  · exact ⟨cut, slot, full, below⟩
  · exact ⟨pos, slot, full, below⟩

/-- Bit `i` of the shifted register, inside the window of `len` bits: the old bit one below, or the top bit at
the bottom. -/
private theorem notes_turing_shift_bit (len reg i : Nat) (lenPos : 0 < len) (lenMax : len ≤ 16) (inside : i < len) :
    (Turing.shift len reg).testBit i = reg.testBit ((i + len - 1) % len) := by
  unfold Turing.shift
  rw [show (65536 : Nat) = 2 ^ 16 by rfl, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  have top : ((reg >>> (len - 1)) % 2).testBit i = (i = 0 && reg.testBit (len - 1)) := by
    rw [show (2 : Nat) = 2 ^ 1 by rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    cases i with
    | zero => simp
    | succ j => simp
  rw [top]
  cases i with
  | zero =>
    simp only [Nat.zero_add, decide_true, Bool.true_and]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp
  | succ j =>
    have e : (j + 1 + len - 1) % len = j := by
      rw [show j + 1 + len - 1 = j + len by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [e]
    simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, decide_false, Bool.false_and, Bool.or_false]
    simp [show j + 1 < 16 by omega]

/-- After `k` shifts, bit `i` of the window is the old bit `k * (len - 1)` places round. -/
private theorem notes_turing_shifts_bit (len reg : Nat) (lenPos : 0 < len) (lenMax : len ≤ 16) :
    ∀ k i, i < len → (Turing.shifts len k reg).testBit i = reg.testBit ((i + k * (len - 1)) % len) := by
  intro k
  induction k generalizing reg with
  | zero => intro i inside; simp [Turing.shifts, Nat.mod_eq_of_lt inside]
  | succ k ih =>
    intro i inside
    simp only [Turing.shifts]
    rw [ih (Turing.shift len reg) i inside, notes_turing_shift_bit len reg _ lenPos lenMax (Nat.mod_lt _ lenPos)]
    congr 1
    rw [show (i + k * (len - 1)) % len + len - 1 = (i + k * (len - 1)) % len + (len - 1) by omega,
      Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show i + (k + 1) * (len - 1) = i + k * (len - 1) + (len - 1) by
        rw [Nat.succ_mul]; omega]

private theorem notes_turing_window_repeats (len reg : Nat) (lenPos : 0 < len) (lenMax : len ≤ 16) :
    Turing.shifts len len reg % 2 ^ len = reg % 2 ^ len := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases inside : i < len
  · simp only [inside, decide_true, Bool.true_and]
    rw [notes_turing_shifts_bit len reg lenPos lenMax len i inside]
    congr 1
    rw [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt inside]
  · simp [inside]

/-- With FLIP at 0 the turing register of `Notes.choose` is the locked shift. -/
private theorem notes_turing_pick_is_shift (len span : Nat) (s : NoteState) (n : Nat) :
    (Notes.picks ⟨6, len, 0⟩ span n s).2.shift = Turing.shifts len n s.shift := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [Notes.picks, Turing.shifts]
    rw [ih]
    rfl

/-- TURING with FLIP at 0 is a locked loop: after `len` picks the register's `len`-bit window is unchanged, so
the notes repeat every `len` picks (once the bits above the window, which the first picks still read, have
been shifted out).
Why it matters: FLIP 0 is an exact loop of LENGTH notes; only FLIP changes it. -/
theorem notes_turing_locked_repeats (len span : Nat) (s : NoteState) (lenPos : 0 < len) (lenMax : len ≤ 16) :
    (Notes.picks ⟨6, len, 0⟩ span len s).2.shift % 2 ^ len = s.shift % 2 ^ len := by
  rw [notes_turing_pick_is_shift]
  exact notes_turing_window_repeats len s.shift lenPos lenMax

/-- Every grammar rewrites every symbol into at least one symbol. -/
private theorem notes_rewrite_nonempty (g s : Nat) : Notes.rewrite g s ≠ [] := by
  unfold Notes.rewrite
  split <;> split <;> (try split) <;> (try split) <;> simp

/-- Every grammar's axiom has a symbol. -/
private theorem notes_axiom_nonempty (g : Nat) : Notes.axiom g ≠ [] := by
  unfold Notes.axiom; split <;> simp

/-- Rewriting a phrase with symbols keeps symbols. -/
private theorem notes_expand_nonempty (g : Nat) : ∀ (d : Nat) (syms : List Nat), syms ≠ [] → Notes.expand g d syms ≠ [] := by
  intro d
  induction d with
  | zero => intro syms h; simpa [Notes.expand] using h
  | succ d ih =>
    intro syms h
    unfold Notes.expand
    apply ih
    cases syms with
    | nil => exact absurd rfl h
    | cons s rest =>
      simp only [List.flatMap_cons, ne_eq, List.append_eq_nil_iff, not_and]
      intro bad; exact absurd bad (notes_rewrite_nonempty g s)

/-- A grammar's phrase is non-empty at every depth.
Why it matters: the GRAMMAR source never has to fall back to a default symbol. -/
theorem notes_grammar_phrase_never_empty (g depth : Nat) : Notes.phraseOf g depth ≠ [] :=
  notes_expand_nonempty g depth (Notes.axiom g) (notes_axiom_nonempty g)

/-- The `n`-th scale tone above `low` is in the scale whenever the scale has more than `n` notes in the five
octaves above `low`.
Why it matters: the CHORD source climbs real scale (or chord) tones; the snap has nothing to fix. -/
theorem notes_scale_tone_in_scale (mask low n : Nat)
    (enough : n < ((List.range 60).filter (fun k => Quantizer.inScale mask (low + k))).length) :
    Quantizer.inScale mask (Notes.scaleTone mask low n) = true := by
  unfold Notes.scaleTone
  simp only
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem enough, Option.getD_some]
  have mem := List.getElem_mem enough
  exact (List.mem_filter.mp mem).2
