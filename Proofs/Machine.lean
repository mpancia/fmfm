import Spec.Machine
import Proofs.Run
import Proofs.Arp

/-- A sum over the four lanes, unrolled. -/
private theorem machine_fold4 (f : Fin 4 → Nat) :
    (List.finRange 4).foldl (fun n i => n + f i) 0 = f 0 + f 1 + f 2 + f 3 := by
  simp [List.finRange, List.ofFn, Fin.foldr, Fin.foldr.loop]

/-- Across the four lanes and the arpeggiator, after any lists of ticks, knob changes and keys from a quiet
machine, note-ons equal note-offs plus what is still sounding, and `stop` leaves nothing sounding.
Why it matters: no stuck notes for the whole instrument, not one part at a time. -/
theorem machine_every_note_on_has_a_note_off (m : Machine) (quiet : m.Quiet) (laneOps : Fin 4 → List Lane.Op)
    (arpOps : List Arp.Op) :
    m.noteOns laneOps arpOps = m.noteOffs laneOps arpOps + (m.run laneOps arpOps).soundingCount ∧
      (m.run laneOps arpOps).stop.Quiet := by
  have lane := fun i => run_every_note_on_has_a_note_off (m.lanes i) (quiet.1 i) (laneOps i)
  have arp := arp_every_note_on_has_a_note_off m.arp quiet.2 arpOps
  refine ⟨?_, fun i => (lane i).2, arp.2⟩
  unfold Machine.noteOns Machine.noteOffs Machine.soundingCount Machine.run
  simp only [machine_fold4]
  have l0 := (lane 0).1; have l1 := (lane 1).1; have l2 := (lane 2).1; have l3 := (lane 3).1
  omega
