import Firmware.Notes

/-- The note memory is consistent with the range and the rule: positions are inside the range, the loop
position is inside the loop, and the loop memory has its full size with every note inside the range. -/
structure NoteState.Valid (span amount : Nat) (s : NoteState) : Prop where
  posBelowSpan : s.pos < span
  slotBelowAmount : s.slot < amount
  regFull : s.reg.length = Notes.regLen
  regBelowSpan : ∀ x ∈ s.reg, x < span

/-! Worked examples: what each algorithm does from a state in a range of 10 positions. -/

/-- The state used below: at position 3, going up, on slot 0 of a loop whose first two notes are 7 and 2. -/
def NoteState.example : NoteState := { pos := 3, rising := true, slot := 0, reg := [7, 2, 0, 0] }

#guard (Notes.choose ⟨2, 1, 0⟩ 10 NoteState.example 0 0 0).offset == 4                    -- up
#guard (Notes.choose ⟨3, 1, 0⟩ 10 NoteState.example 0 0 0).offset == 2                    -- down
#guard (Notes.choose ⟨3, 1, 0⟩ 10 { NoteState.example with pos := 0 } 0 0 0).offset == 9   -- down wraps
#guard (Notes.choose ⟨4, 1, 0⟩ 10 { NoteState.example with pos := 9 } 0 0 0).offset == 8   -- bounce turns at the top
#guard (Notes.choose ⟨1, 2, 0⟩ 10 NoteState.example 0 0 0).offset == 1                    -- walk: smallest step, down 2
#guard (Notes.choose ⟨1, 2, 0⟩ 10 NoteState.example 0 4 0).offset == 5                    -- walk: largest step, up 2
#guard (Notes.choose ⟨5, 2, 0⟩ 10 NoteState.example 6 6 50).offset == 7                   -- loop: replays slot 0
#guard (Notes.choose ⟨5, 2, 0⟩ 10 NoteState.example 6 6 50).state.slot == 1               -- and moves to slot 1
#guard (Notes.choose ⟨5, 2, 100⟩ 10 NoteState.example 6 6 50).offset == 6                 -- loop: mutation takes the new note
#guard (Notes.choose ⟨0, 1, 0⟩ 10 NoteState.example 6 0 0).offset == 6                    -- random: the drawn note
