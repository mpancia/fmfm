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
def NoteState.example : NoteState :=
  { pos := 3, rising := true, slot := 0, reg := [7, 2, 0, 0], cursor := 0, shift := 0, chain := [], last := 3, phrase := 0 }

#guard (Notes.choose ⟨2, 1, 0⟩ 10 4095 48 NoteState.example 0 0 0).offset == 4  -- up
#guard (Notes.choose ⟨3, 1, 0⟩ 10 4095 48 NoteState.example 0 0 0).offset == 2  -- down
#guard (Notes.choose ⟨3, 1, 0⟩ 10 4095 48 { NoteState.example with pos := 0 } 0 0 0).offset == 9  -- down wraps
-- bounce turns at the top
#guard (Notes.choose ⟨4, 1, 0⟩ 10 4095 48 { NoteState.example with pos := 9 } 0 0 0).offset == 8
#guard (Notes.choose ⟨1, 2, 0⟩ 10 4095 48 NoteState.example 0 0 0).offset == 1  -- walk: smallest step, down 2
#guard (Notes.choose ⟨1, 2, 0⟩ 10 4095 48 NoteState.example 0 4 0).offset == 5  -- walk: largest step, up 2
#guard (Notes.choose ⟨5, 2, 0⟩ 10 4095 48 NoteState.example 6 6 50).offset == 7  -- loop: replays slot 0
#guard (Notes.choose ⟨5, 2, 0⟩ 10 4095 48 NoteState.example 6 6 50).state.slot == 1  -- and moves to slot 1
-- loop: mutation takes the new note
#guard (Notes.choose ⟨5, 2, 100⟩ 10 4095 48 NoteState.example 6 6 50).offset == 6
#guard (Notes.choose ⟨0, 1, 0⟩ 10 4095 48 NoteState.example 6 0 0).offset == 6  -- random: the drawn note

-- turing: the register shifts and the low byte sets the pitch (register 0x00FF, length 8: the top bit 1 recycles)
#guard (Notes.choose ⟨6, 8, 0⟩ 10 4095 48 { NoteState.example with shift := 0x00FF } 0 0 50).state.shift == 0x01FF
#guard (Notes.choose ⟨6, 8, 100⟩ 10 4095 48 { NoteState.example with shift := 0x00FF } 0 0 50).state.shift == 0x01FE
-- markov: from a repeat (move 3) in the REPEATS style the pick of 0 lands on a move down, three positions at most
#guard (Notes.choose ⟨8, 3, 0⟩ 10 4095 48 NoteState.example 0 0 50).offset == 0
#guard (Notes.choose ⟨8, 3, 0⟩ 10 4095 48 NoteState.example 5 0 50).offset == 3
-- grammar: the fibonacci phrase at depth 2 is A B A; its symbols step up, skip up, step up
#guard Notes.phraseOf 0 2 == [0, 1, 0]
#guard (Notes.choose ⟨9, 1, 50⟩ 10 4095 48 NoteState.example 0 0 0).offset == 4
-- chord: the next tone of C major above C3 (48), then the one after
#guard (Notes.choose ⟨10, 3, 0⟩ 12 0xAB5 48 NoteState.example 0 0 50).offset == 2
#guard (Notes.choose ⟨10, 3, 0⟩ 12 0xAB5 48 { NoteState.example with slot := 1 } 0 0 50).offset == 4
-- the keys teach: the step sequencer writes slot 0 and moves on; the markov chain counts a move up by two
#guard (Notes.learn ⟨7, 4, 0⟩ 10 NoteState.example 5).reg == [5, 2, 0, 0]
#guard (Notes.learn ⟨7, 4, 0⟩ 10 NoteState.example 5).cursor == 1
#guard (Notes.learn ⟨8, 1, 0⟩ 10 { NoteState.example with chain := List.replicate 49 0 } 5).chain.getD (3 * 7 + 5) 0 == 1

/-- The memory after `n` picks of an algorithm whose random inputs do not matter (up, down, bounce), and the
pitches those picks gave, oldest first. -/
def Notes.picks (rule : NoteRule) (span : Nat) : Nat → NoteState → List Nat × NoteState
  | 0, s => ([], s)
  | n + 1, s =>
    let c := Notes.choose rule span 4095 48 s 0 0 0
    let (rest, final) := Notes.picks rule span n c.state
    (c.offset :: rest, final)
