import Firmware.Rhythm

/-- How many steps of a bar of `n` steps satisfy `f`. -/
def Rhythm.count (f : Nat → Bool) (n : Nat) : Nat := ((List.range n).filter f).length

/-! Worked examples: a 3-in-8 bar, turned, accented, and run through the automaton. -/

-- 3 hits in 8 steps turned by 2: hits at 1, 4 and 7 (the plain bar has them at 2, 5 and 7)
#guard (List.range 8).filter (Rhythm.hit ⟨1, 2, 0, 0, 1, 1, 0⟩ 3 8) == [1, 4, 7]
#guard (List.range 8).filter (Euclid.hit 3 8) == [2, 5, 7]
-- the turn keeps three hits for any turn
#guard (List.range 8).all fun r => Rhythm.count (Rhythm.hit ⟨1, r, 0, 0, 1, 1, 0⟩ 3 8) 8 == 3
-- one accent of three hits falls on the last hit
#guard (List.range 8).filter (Rhythm.accent ⟨1, 0, 1, 0, 1, 1, 0⟩ 3 8) == [7]
-- rule 90 from one cell in 8 draws the Sierpinski rows; rule 204 freezes; rule 0 dies; rule 255 fills
#guard (List.range 4).map (fun g => (List.range g).foldl (fun r _ => Automaton.step 90 8 r) 0x10) == [0x10, 0x28, 0x44, 0xAA]
#guard Automaton.step 204 8 0x2D == 0x2D
#guard Automaton.step 0 8 0x2D == 0
#guard Automaton.step 255 8 0x2D == 0xFF
-- the ratchet: sub-hit 0 is the pulse, the rest follow at even spacing in a step of 24 ticks
#guard (List.range 24).filterMap (Rhythm.subIndex 24 3) == [0, 1, 2]
#guard (List.range 24).filter (fun c => (Rhythm.subIndex 24 3 c).isSome) == [0, 8, 16]
