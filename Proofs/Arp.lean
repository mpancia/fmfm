import Spec.Arp
import Proofs.Random

/-- A random draw below a limit from 1 to 65535 is below it. -/
private theorem arp_draw_below (rng : UInt32) (limit : Nat) (positive : 0 < limit) (small : limit ≤ 65535) :
    (Random.below rng limit.toUInt32).toNat < limit := by
  have limitSmall : limit.toUInt32.toNat = limit := by simp; omega
  have := random_below_lt rng limit.toUInt32 (by rw [limitSmall]; exact positive)
    (by rw [limitSmall]; exact small)
  rwa [limitSmall] at this

/-- Inserting into a sorted list adds exactly that note. -/
private theorem arp_mem_insertSorted (n x : Nat) : ∀ l : List Nat, x ∈ Arp.insertSorted n l ↔ x = n ∨ x ∈ l := by
  intro l
  induction l with
  | nil => simp [Arp.insertSorted]
  | cons y ys ih =>
    unfold Arp.insertSorted
    split
    · simp
    · simp only [List.mem_cons, ih]
      constructor
      · intro h; rcases h with h | h | h <;> simp [h]
      · intro h; rcases h with h | h | h <;> simp [h]

/-- Sorting keeps the same notes. -/
private theorem arp_mem_sorted (x : Nat) (l : List Nat) : x ∈ Arp.sorted l ↔ x ∈ l := by
  unfold Arp.sorted
  induction l with
  | nil => simp
  | cons y ys ih => simp [List.foldr_cons, arp_mem_insertSorted, ih]

/-- Inserting adds one. -/
private theorem arp_length_insertSorted (n : Nat) : ∀ l : List Nat, (Arp.insertSorted n l).length = l.length + 1 := by
  intro l
  induction l with
  | nil => rfl
  | cons y ys ih => unfold Arp.insertSorted; split <;> simp [ih]

/-- Sorting keeps the length. -/
private theorem arp_length_sorted (l : List Nat) : (Arp.sorted l).length = l.length := by
  unfold Arp.sorted
  induction l with
  | nil => rfl
  | cons y ys ih => simp [List.foldr_cons, arp_length_insertSorted, ih]

/-- The pattern has `octaves` times the held notes. -/
private theorem arp_length_pattern (a : Arp) : a.pattern.length = max 1 a.octaves * a.held.length := by
  unfold Arp.pattern
  rw [List.length_flatMap]
  have each : ∀ o, ((if a.mode = 5 then a.held else Arp.sorted a.held).map (· + 12 * o)).length = a.held.length := by
    intro o
    rw [List.length_map]
    split
    · rfl
    · exact arp_length_sorted a.held
  simp only [each, List.map_const', List.length_range, List.sum_replicate_nat]

/-- Every note of the pattern is a held note raised by whole octaves, fewer than `octaves` of them. -/
private theorem arp_pattern_mem (a : Arp) (n : Nat) (mem : n ∈ a.pattern) :
    ∃ h ∈ a.held, ∃ o, o < max 1 a.octaves ∧ n = h + 12 * o := by
  unfold Arp.pattern at mem
  simp only [List.mem_flatMap, List.mem_range, List.mem_map] at mem
  obtain ⟨o, oLt, h, hMem, rfl⟩ := mem
  refine ⟨h, ?_, o, oLt, rfl⟩
  split at hMem
  · exact hMem
  · exact (arp_mem_sorted h a.held).mp hMem

/-- The pattern is empty exactly when nothing is held. -/
private theorem arp_pattern_empty (a : Arp) : a.pattern.isEmpty = true ↔ a.held = [] := by
  unfold Arp.pattern
  cases h : a.held with
  | nil => simp [Arp.sorted, List.flatMap]
  | cons x xs =>
    simp only [List.isEmpty_iff, List.flatMap_eq_nil_iff, List.mem_range, List.map_eq_nil_iff, reduceCtorEq, iff_false]
    intro all
    have := all 0 (by omega)
    split at this
    · simp_all
    · have : x ∈ Arp.sorted (x :: xs) := (arp_mem_sorted x _).mpr (List.mem_cons_self)
      simp_all

/-- The position a step reads is inside the pattern. -/
private theorem arp_step_inside (a : Arp) (len : Nat) (positive : 0 < len) (small : len ≤ 65535) :
    (a.step len).1 < len := by
  unfold Arp.step
  have := Nat.mod_lt a.pos positive
  split
  · exact this
  · by_cases r : a.rising <;> simp [r] <;> split <;> omega
  · exact arp_draw_below a.rng len positive small
  · exact this

/-- Every note the arpeggiator starts is a note you are holding, raised by fewer than `octaves` octaves.
Why it matters: the arpeggiator can only play what you play; it never adds a note of its own, whichever mode
and however it is set. -/
theorem arp_note_is_held (a : Arp) (valid : Arp.Valid a) (note : Nat) (starts : a.tick.on = some note) :
    ∃ h ∈ a.held, ∃ o, o < max 1 a.octaves ∧ note = h + 12 * o := by
  unfold Arp.tick at starts
  dsimp only at starts
  split at starts
  · rename_i cond
    generalize hs : a.step a.pattern.length = st at starts
    obtain ⟨here, pos, rising⟩ := st
    dsimp only at starts
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, ne_eq, decide_eq_true_eq] at cond
    simp only [Option.some.injEq] at starts
    subst starts
    have len : 0 < a.pattern.length := by
      cases h : a.pattern with
      | nil => simp [h] at cond
      | cons x xs => simp
    have small : a.pattern.length ≤ 65535 := by
      have few := valid.heldFew
      have oct := valid.octavesFit
      rw [arp_length_pattern]
      have : max 1 a.octaves ≤ 3 := by omega
      exact Nat.le_trans (Nat.mul_le_mul this few) (by decide)
    have inside := arp_step_inside a a.pattern.length len small
    rw [hs] at inside
    apply arp_pattern_mem
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside, Option.getD_some]
    exact List.getElem_mem inside
  · split at starts <;> simp at starts

/-- A fresh arpeggiator is consistent, for any step.
Why it matters: the arpeggiator starts in a state the rest of the firmware can rely on, whatever the knobs say. -/
theorem arp_make_valid (div : Nat) (seed : UInt32) : Arp.Valid (Arp.make div seed) := by
  unfold Arp.make Arp.clamp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> omega

/-- Changing the settings keeps a consistent arpeggiator consistent, whatever numbers are given.
Why it matters: turning the ARP knobs mid-phrase cannot leave a timer or counter out of range. -/
theorem arp_set_valid (a : Arp) (valid : Arp.Valid a) (mode octaves div gate : Nat) :
    Arp.Valid (a.set mode octaves div gate) := by
  have timer := valid.soundingHasTimer
  obtain ⟨_, _, _, _, _, _, held, few, _, _, _⟩ := valid
  unfold Arp.set Arp.clamp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, held, few, ?_, ?_, ?_⟩ <;> simp_all <;>
    first | omega | exact Nat.mod_lt _ (by omega)

/-- Pressing, releasing or clearing keys keeps a consistent arpeggiator consistent.
Why it matters: whatever you play, and however many keys, the held set stays playable and small. -/
theorem arp_keys_valid (a : Arp) (valid : Arp.Valid a) (note : Nat) :
    Arp.Valid (a.press note) ∧ Arp.Valid (a.release note) ∧ Arp.Valid a.clear := by
  obtain ⟨m, o1, o2, d, g1, g2, held, few, c, t, w⟩ := valid
  refine ⟨?_, ?_, ?_⟩
  · unfold Arp.press
    split
    · rename_i cond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
      refine ⟨m, o1, o2, d, g1, g2, ?_, ?_, c, t, w⟩
      · intro n mem
        rw [List.mem_append, List.mem_singleton] at mem
        rcases mem with mem | rfl
        · exact held n mem
        · exact cond.1.1
      · simp; omega
    · exact ⟨m, o1, o2, d, g1, g2, held, few, c, t, w⟩
  · unfold Arp.release
    refine ⟨m, o1, o2, d, g1, g2, ?_, ?_, c, t, w⟩
    · intro n mem; exact held n (List.mem_filter.mp mem).1
    · exact Nat.le_trans (List.length_filter_le _ _) few
  · unfold Arp.clear
    exact ⟨m, o1, o2, d, g1, g2, by simp, by simp, c, t, w⟩

/-- A tick keeps a consistent arpeggiator consistent.
Why it matters: however long it runs, the counters stay in range and the sounding note and its timer agree. -/
theorem arp_tick_valid (a : Arp) (valid : Arp.Valid a) : Arp.Valid a.tick := by
  have timer := valid.soundingHasTimer
  obtain ⟨m, o1, o2, d, g1, g2, held, few, c, t, w⟩ := valid
  have count : (Divider.tick a.div a.count).1 < a.div := by
    unfold Divider.tick; split <;> omega
  unfold Arp.tick
  dsimp only
  split
  · generalize a.step a.pattern.length = st
    obtain ⟨here, pos, rising⟩ := st
    refine ⟨m, o1, o2, d, g1, g2, held, few, count, ?_, ?_⟩
    · simp; omega
    · simp
  · split
    · exact ⟨m, o1, o2, d, g1, g2, held, few, count, by simp, by simp⟩
    · rename_i more
      refine ⟨m, o1, o2, d, g1, g2, held, few, count, ?_, ?_⟩
      · simp only []; rw [timer]; omega
      · simp only []; omega

/-- Moving the clock on does not touch the sounding note. -/
private theorem arp_tick_balance (a : Arp) :
    (if a.tick.on.isSome then 1 else 0) + a.soundingCount =
      (if a.tick.off.isSome then 1 else 0) + a.tick.soundingCount := by
  unfold Arp.soundingCount Arp.tick
  dsimp only
  cases h : a.playing <;> split <;> (try split) <;> (try generalize a.step a.pattern.length = st) <;>
    (try obtain ⟨_, _, _⟩ := st) <;> simp [h]

/-- Keys and settings keep the sounding note. -/
private theorem arp_others_keep_sounding (a : Arp) (op : Arp.Op) (notTick : op ≠ .tick) :
    (a.apply op).playing = a.playing := by
  cases op with
  | tick => exact absurd rfl notTick
  | press n => simp only [Arp.apply, Arp.press]; split <;> rfl
  | release n => rfl
  | clear => rfl
  | set m o d g => rfl

/-- On-count and off-count of a trace, one pair at a time. -/
private theorem arp_counts_cons (x : Option Nat × Option Nat) (t : List (Option Nat × Option Nat)) :
    Arp.noteOns (x :: t) = (if x.2.isSome then 1 else 0) + Arp.noteOns t ∧
      Arp.noteOffs (x :: t) = (if x.1.isSome then 1 else 0) + Arp.noteOffs t := by
  unfold Arp.noteOns Arp.noteOffs
  constructor <;> simp [List.filter_cons] <;> split <;> simp <;> omega

/-- Over any run, note-ons plus what sounded at the start equal note-offs plus what sounds at the end. -/
private theorem arp_balance (ops : List Arp.Op) : ∀ a : Arp,
    Arp.noteOns (a.trace ops) + a.soundingCount = Arp.noteOffs (a.trace ops) + (a.run ops).soundingCount := by
  induction ops with
  | nil => intro a; simp [Arp.trace, Arp.run, Arp.noteOns, Arp.noteOffs]
  | cons op rest ih =>
    intro a
    cases op with
    | tick =>
      have step := arp_tick_balance a
      have later := ih a.tick
      have ⟨ons, offs⟩ := arp_counts_cons (a.tick.off, a.tick.on) (a.tick.trace rest)
      simp only [Arp.trace, Arp.run, Arp.apply] at *
      omega
    | press n =>
      have keep := arp_others_keep_sounding a (.press n) (by simp)
      simp only [Arp.trace, Arp.run]
      rw [show a.soundingCount = (a.apply (.press n)).soundingCount by simp [Arp.soundingCount, keep]]
      exact ih _
    | release n =>
      have keep := arp_others_keep_sounding a (.release n) (by simp)
      simp only [Arp.trace, Arp.run]
      rw [show a.soundingCount = (a.apply (.release n)).soundingCount by simp [Arp.soundingCount, keep]]
      exact ih _
    | clear =>
      have keep := arp_others_keep_sounding a .clear (by simp)
      simp only [Arp.trace, Arp.run]
      rw [show a.soundingCount = (a.apply .clear).soundingCount by simp [Arp.soundingCount, keep]]
      exact ih _
    | set m o d g =>
      have keep := arp_others_keep_sounding a (.set m o d g) (by simp)
      simp only [Arp.trace, Arp.run]
      rw [show a.soundingCount = (a.apply (.set m o d g)).soundingCount by simp [Arp.soundingCount, keep]]
      exact ih _

/-- Every note the arpeggiator starts during a run is stopped: after any sequence of ticks, keys and setting
changes, note-ons equal note-offs plus the one note still sounding, which `silence` stops.
Why it matters: letting go of the keys, or stopping, never leaves an arpeggio note hanging. -/
theorem arp_every_note_on_has_a_note_off (a : Arp) (fresh : a.playing = none) (ops : List Arp.Op) :
    Arp.noteOns (a.trace ops) = Arp.noteOffs (a.trace ops) + (a.run ops).soundingCount ∧
      (a.run ops).silence.playing = none := by
  have balance := arp_balance ops a
  have start : a.soundingCount = 0 := by simp [Arp.soundingCount, fresh]
  exact ⟨by omega, rfl⟩

/-- One UP tick with a step a tick: the note at the position, and the position moves on; nothing that shapes
the pattern changes. -/
private theorem arp_up_tick (a : Arp) (mode : a.mode = 1) (div : a.div = 1) (held : a.held ≠ []) :
    a.tick.on = some (a.pattern.getD (a.pos % a.pattern.length) 0) ∧
      a.tick.pos = (a.pos % a.pattern.length + 1) % a.pattern.length ∧ a.tick.held = a.held ∧
      a.tick.mode = a.mode ∧ a.tick.octaves = a.octaves ∧ a.tick.div = a.div := by
  have step : a.atStep = true := by unfold Arp.atStep Divider.tick; simp [div]
  have nonempty : a.pattern.isEmpty = false := by
    have := arp_pattern_empty a
    cases h : a.pattern.isEmpty
    · rfl
    · exact absurd (this.mp h) held
  unfold Arp.tick
  dsimp only
  rw [step, nonempty]
  simp only [mode, Bool.true_and, ne_eq, Nat.one_ne_zero, decide_true, Bool.not_false, ite_true]
  unfold Arp.step
  simp only [mode]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The pattern does not change across UP ticks. -/
private theorem arp_up_pattern (a : Arp) (mode : a.mode = 1) (div : a.div = 1) (held : a.held ≠ []) :
    a.tick.pattern = a.pattern := by
  have ⟨_, _, h, m, o, _⟩ := arp_up_tick a mode div held
  unfold Arp.pattern
  rw [h, m, o]

/-- After `n` UP ticks from position `p`, the notes played are the pattern read from `p` on, round and round. -/
private theorem arp_up_played (n : Nat) : ∀ (a : Arp), a.mode = 1 → a.div = 1 → a.held ≠ [] →
    a.played n = (List.range n).map (fun k => a.pattern.getD ((a.pos + k) % a.pattern.length) 0) := by
  induction n with
  | zero => intro a _ _ _; rfl
  | succ n ih =>
    intro a mode div held
    have ⟨on, pos, h, m, o, d⟩ := arp_up_tick a mode div held
    have pat := arp_up_pattern a mode div held
    have next := ih a.tick (by rw [m, mode]) (by rw [d, div]) (by rw [h]; exact held)
    simp only [Arp.played, on, List.range_succ_eq_map, List.map_cons, List.map_map, next, pat, pos]
    rw [List.singleton_append, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro k _
    simp only [Function.comp, Nat.succ_eq_add_one]
    congr 1
    rw [Nat.mod_add_mod, Nat.add_assoc, Nat.mod_add_mod, Nat.add_comm 1 k]

/-- UP with a step a tick, from the start of the pattern, plays the pattern through note for note: as many
ticks as the pattern has notes start exactly the pattern, in order.
Why it matters: UP is a rising run over exactly what you hold, each note once, in order, before it comes round;
the same reading gives every later lap, since the position comes back to the start. -/
theorem arp_up_plays_pattern (a : Arp) (mode : a.mode = 1) (div : a.div = 1) (start : a.pos = 0)
    (held : a.held ≠ []) : a.played a.pattern.length = a.pattern := by
  rw [arp_up_played a.pattern.length a mode div held, start]
  apply List.ext_getElem
  · simp
  · intro i lt _
    simp only [List.getElem_map, List.getElem_range, Nat.zero_add]
    rw [List.length_map, List.length_range] at lt
    rw [Nat.mod_eq_of_lt lt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem lt, Option.getD_some]
