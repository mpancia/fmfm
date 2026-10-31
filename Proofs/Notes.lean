import Spec.Notes
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

/-- A fresh note memory is consistent for any range from 1 to 65535 positions and any loop length from 1 to 16.
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

/-- Whichever algorithm picks, the pitch is inside the range and the memory stays consistent.
Why it matters: the note can never land outside the range the lane was given, and no algorithm can corrupt
the memory the next pick depends on, however long it runs. -/
theorem notes_choose_stays_in_range (rule : NoteRule) (span : Nat) (s : NoteState) (any step chance : Nat)
    (positive : 0 < span) (loopLength : 0 < rule.amount) (fits : rule.amount ≤ Notes.regLen)
    (valid : NoteState.Valid span rule.amount s) (anyBelow : any < span) :
    (Notes.choose rule span s any step chance).offset < span ∧
      NoteState.Valid span rule.amount (Notes.choose rule span s any step chance).state := by
  obtain ⟨pos, slot, full, below⟩ := valid
  unfold Notes.choose
  split
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> (try split) <;> omega
  · exact ⟨Nat.mod_lt _ positive, Nat.mod_lt _ positive, slot, full, below⟩
  · exact ⟨Nat.mod_lt _ positive, Nat.mod_lt _ positive, slot, full, below⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only <;> (try split) <;> (try split) <;> (try dsimp only) <;>
      first | omega | assumption | skip
  · have inRange : s.slot < s.reg.length := by omega
    have kept : s.reg.getD s.slot 0 < span := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inRange, Option.getD_some]
      exact below _ (List.getElem_mem inRange)
    have value : (if chance < rule.mutate then any else s.reg.getD s.slot 0) < span := by split <;> assumption
    obtain ⟨len, mem⟩ := notes_set_keeps_memory span s full below s.slot _ value
    exact ⟨value, pos, Nat.mod_lt _ loopLength, len, mem⟩
  · exact ⟨anyBelow, anyBelow, slot, full, below⟩
