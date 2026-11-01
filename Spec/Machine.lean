import Spec.Run
import Spec.Arp

/-! The whole instrument as the proofs see it: four lanes and the arpeggiator, each run by its own list of
operations (the firmware's `clock_poll` ticks them all on a tick; the knobs and keys reach one at a time), and
PLAY stopping, which silences every one of them. -/

/-- The parts that start and stop notes. -/
structure Machine where
  lanes : Fin 4 → Lane
  arp : Arp

/-- Everything that sounds, on every tick of a run: note-ons and note-offs over the five parts. -/
def Machine.noteOns (m : Machine) (laneOps : Fin 4 → List Lane.Op) (arpOps : List Arp.Op) : Nat :=
  (List.finRange 4).foldl (fun n i => n + Lane.noteOns ((m.lanes i).trace (laneOps i))) 0 +
    Arp.noteOns (m.arp.trace arpOps)

/-- The note-offs, likewise. -/
def Machine.noteOffs (m : Machine) (laneOps : Fin 4 → List Lane.Op) (arpOps : List Arp.Op) : Nat :=
  (List.finRange 4).foldl (fun n i => n + Lane.noteOffs ((m.lanes i).trace (laneOps i))) 0 +
    Arp.noteOffs (m.arp.trace arpOps)

/-- The machine after the run. -/
def Machine.run (m : Machine) (laneOps : Fin 4 → List Lane.Op) (arpOps : List Arp.Op) : Machine :=
  ⟨fun i => (m.lanes i).run (laneOps i), m.arp.run arpOps⟩

/-- How many notes the parts count as sounding. -/
def Machine.soundingCount (m : Machine) : Nat :=
  (List.finRange 4).foldl (fun n i => n + (m.lanes i).soundingCount) 0 + m.arp.soundingCount

/-- PLAY stopping: every part silenced. -/
def Machine.stop (m : Machine) : Machine := ⟨fun i => (m.lanes i).silence, m.arp.silence⟩

/-- Nothing sounding anywhere. -/
def Machine.Quiet (m : Machine) : Prop := (∀ i, (m.lanes i).playing = none) ∧ m.arp.playing = none
