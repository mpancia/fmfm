import Spec.Lane
import Proofs.Random
import Proofs.Quantizer
import Proofs.Notes

/-- A random draw below a limit from 1 to 65535 is below it. -/
private theorem lane_draw_below (rng : UInt32) (limit : Nat) (positive : 0 < limit) (small : limit ≤ 65535) :
    (Random.below rng limit.toUInt32).toNat < limit := by
  have limitSmall : limit.toUInt32.toNat = limit := by simp; omega
  have := random_below_lt rng limit.toUInt32 (by rw [limitSmall]; exact positive)
    (by rw [limitSmall]; exact small)
  rwa [limitSmall] at this

/-- Whatever settings are asked for, `make` gives a consistent lane.
Why it matters: bad numbers from the screen or a saved file cannot put a lane into a state the rest of the
code does not expect. -/
theorem lane_make_valid (hits steps div mask low span : Nat) (seed : UInt32) :
    Lane.Valid (Lane.make hits steps div mask low span seed) := by
  have notes : ∀ n, 0 < n → n ≤ 108 → NoteState.Valid n 4 (Notes.start n seed) :=
    fun n positive small => notes_start_valid n 4 seed positive (by omega) (by omega)
  have spanBounds : 1 ≤ Lane.clamp 1 (120 - Lane.clamp 12 96 low) span ∧
      Lane.clamp 1 (120 - Lane.clamp 12 96 low) span ≤ 108 := by
    unfold Lane.clamp; omega
  have startValid := notes _ (by omega) spanBounds.2
  unfold Lane.make Lane.gateFor Lane.cleanMask
  by_cases empty : mask % 4096 = 0 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [empty, Lane.clamp, Notes.regLen] at * <;> omega

/-- `reconfigure` keeps a consistent lane consistent, even for nonsense settings.
Why it matters: turning a knob mid-song can never leave the lane with a position or timer out of range. -/
theorem lane_reconfigure_valid (l : Lane) (valid : Lane.Valid l) (hits steps div mask : Nat) :
    Lane.Valid (Lane.reconfigure l hits steps div mask) := by
  have timer := valid.soundingHasTimer
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := valid
  unfold Lane.reconfigure Lane.gateFor Lane.cleanMask Lane.clamp
  by_cases empty : mask % 4096 = 0 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp_all <;> first | omega | exact Nat.mod_lt _ (by omega)

/-- Changing the note algorithm keeps a consistent lane consistent, whatever numbers are given.
Why it matters: switching a lane from random to loop in the middle of a song cannot leave its loop position
outside the loop. -/
theorem lane_set_notes_valid (l : Lane) (valid : Lane.Valid l) (algo prob amount mutate : Nat) :
    Lane.Valid (Lane.setNotes l algo prob amount mutate) := by
  have timer := valid.soundingHasTimer
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨pos, slot, full, below⟩, _, _, _, _⟩ := valid
  unfold Lane.setNotes Lane.clamp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp_all [Notes.regLen] <;>
    first | omega | exact ⟨pos, Nat.mod_lt _ (by omega), full, below⟩ | skip

/-- The step counter and the clock count stay in range as the lane moves on one tick. -/
private theorem lane_moved_counters (l : Lane) (valid : Lane.Valid l) :
    l.moved.count < l.div ∧ l.moved.step < l.steps ∧ l.moved.div = l.div ∧ l.moved.steps = l.steps := by
  have count := valid.countBelowDiv
  have step := valid.stepBelowSteps
  have steps := valid.stepsPositive
  refine ⟨?_, ?_, rfl, rfl⟩
  · unfold Lane.moved Divider.tick; dsimp only; split <;> omega
  · unfold Lane.moved; dsimp only; split
    · exact Nat.mod_lt _ (by omega)
    · exact step

/-- The note algorithm's pick: in range, with a consistent memory. -/
private theorem lane_pick_ok (l : Lane) (valid : Lane.Valid l) :
    l.noteChoice.offset < l.span ∧ NoteState.Valid l.span l.rule.amount l.noteChoice.state :=
  notes_choose_stays_in_range l.rule l.span l.mask l.low l.notes _ _ _
    (by have := valid.spanPositive; omega) valid.loopLengthPositive valid.loopLengthFits valid.notesValid
    (lane_draw_below _ _ (by have := valid.spanPositive; omega) (by have := valid.spanFits; omega))

/-- The gate a tick starts: at least one tick, and never longer than the lane's gate. -/
private theorem lane_gate_now (l : Lane) (gate : 1 ≤ l.gate) : 1 ≤ l.gateNow ∧ l.gateNow ≤ l.gate := by
  unfold Lane.gateNow; split <;> omega

/-- A tick keeps a consistent lane consistent.
Why it matters: however long the music runs, the counters stay in range, the note memory stays sound, and the
sounding note and its timer stay in step. -/
theorem lane_tick_valid (l : Lane) (valid : Lane.Valid l) : Lane.Valid (Lane.tick l) := by
  have ⟨countOk, stepOk, divSame, stepsSame⟩ := lane_moved_counters l valid
  have ⟨_, choiceOk⟩ := lane_pick_ok l valid
  have ⟨gateLo, gateHi⟩ := lane_gate_now l valid.gatePositive
  have timer := valid.soundingHasTimer
  have notesOk := valid.notesValid
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := valid
  unfold Lane.tick
  split
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | exact choiceOk | (simp_all [Lane.moved] <;> omega)
  · split
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        first | exact notesOk | (simp_all [Lane.moved] <;> omega)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        first | exact notesOk | (simp_all [Lane.moved] <;> omega)

/-- When a sounding note's gate runs out, the tick reports it as stopped.
Why it matters: no note stays on after its gate, so no stuck notes. -/
theorem lane_gate_end_stops_note (l : Lane) (note : Nat) (playing : l.playing = some note)
    (ending : l.gateLeft ≤ 1) : (Lane.tick l).off = some note := by
  unfold Lane.tick
  split
  · simp [playing]
  · simp [playing]

/-- A tick that starts a note also stops the one sounding before it.
Why it matters: a lane never has two notes on at once, so every note-on has exactly one note-off. -/
theorem lane_new_note_stops_old (l : Lane) (note : Nat) (starts : (Lane.tick l).on = some note) :
    (Lane.tick l).off = l.playing := by
  unfold Lane.tick at *
  split at starts <;> split <;> first | rfl | (split at starts <;> simp_all)

/-- A note starts only on a step the rhythm marks as a hit (the step the note belongs to: for a ratchet's
sub-hit, the step that just pulsed).
Why it matters: the rhythm's pattern is respected, whichever rhythm source makes it; a rest never plays,
whatever the note algorithm or the play chance say. -/
theorem lane_note_only_on_hit (l : Lane) (note : Nat) (starts : (Lane.tick l).on = some note) :
    Rhythm.hit l.rhythm l.hits l.steps l.hitStep = true := by
  have plays : l.plays = true → Rhythm.hit l.rhythm l.hits l.steps l.hitStep = true := by
    intro h
    unfold Lane.plays Lane.isHit at h
    simp only [Bool.and_eq_true] at h
    split at h
    · simp at h
    · simp only [Bool.and_eq_true] at h
      exact h.1.1
  unfold Lane.tick at starts
  split at starts
  · exact plays (by assumption)
  · split at starts <;> simp at starts

/-- A note a tick starts is a valid MIDI note and is in the lane's scale.
Why it matters: the lane can never play a note the voices reject, or a note outside the key you chose,
whichever note algorithm it uses. -/
theorem lane_note_in_scale (l : Lane) (valid : Lane.Valid l) (note : Nat)
    (starts : (Lane.tick l).on = some note) : note ≤ 127 ∧ Quantizer.inScale l.mask note = true := by
  have ⟨offset, _⟩ := lane_pick_ok l valid
  have low := valid.lowFloor
  have fits := valid.spanFits
  unfold Lane.tick at starts
  split at starts
  · simp only [Option.some.injEq] at starts
    subst starts
    have near := quantizer_snap_is_near l.mask (l.low + l.noteChoice.offset) valid.maskSmall
      valid.maskNotEmpty (by omega)
    exact ⟨by omega, quantizer_snap_in_scale _ _ valid.maskSmall valid.maskNotEmpty (by omega)⟩
  · split at starts <;> simp at starts

/-- Silencing a consistent lane leaves it consistent.
Why it matters: stopping the clock cannot leave the lane with a timer and no note, or a note and no timer. -/
theorem lane_silence_valid (l : Lane) (valid : Lane.Valid l) : Lane.Valid l.silence := by
  have timer := valid.soundingHasTimer
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := valid
  unfold Lane.silence
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all <;> omega

/-- Silencing reports the sounding note as stopped and leaves nothing sounding.
Why it matters: pressing stop never leaves a note hanging. -/
theorem lane_silence_stops_note (l : Lane) : l.silence.off = l.playing ∧ l.silence.playing = none := by
  simp [Lane.silence]

/-- Applying a lane's own settings back to it changes nothing, for a consistent lane whose settings are the
ones the knobs can reach (steps up to 32, speed up to 96 ticks, algorithm 0 to 10, mutation up to 100 percent,
a rhythm source in range with a live automaton row, the step sequencer's cursor inside its loop) and whose
gate is the one its speed gives. `make`, `reconfigure`, `setNotes` and `setRhythm` only ever produce such
lanes.
Why it matters: saving a patch and loading it again, or redrawing a knob at its current value, cannot alter
the music by a tick: the lane is exactly where it was. -/
theorem lane_reconfigure_self (l : Lane) (valid : Lane.Valid l) (stepsMax : l.steps ≤ 32)
    (divMax : l.div ≤ 96) (algoMax : l.rule.algo ≤ 10) (mutateMax : l.rule.mutate ≤ 100) (gate : l.gate = Lane.gateFor l.div)
    (cursor : l.notes.cursor < l.rule.amount) (kind : l.rhythm.kind ≤ 3) (rotate : l.rhythm.rotate < l.steps)
    (accents : l.rhythm.accents ≤ l.hits) (rule : l.rhythm.rule < 256) (ratchet : 1 ≤ l.rhythm.ratchet ∧ l.rhythm.ratchet ≤ 4)
    (subHits : l.rhythm.subHits ≤ l.rhythm.ratchet) (row : l.rhythm.row < 2 ^ l.steps) (live : l.rhythm.row ≠ 0) :
    l.reconfigure l.hits l.steps l.div l.mask = l ∧
      l.setNotes l.rule.algo l.prob l.rule.amount l.rule.mutate = l := by
  obtain ⟨steps, hits, div, maskNe, maskSmall, _, _, _, _, _, prob, amount, amountFits, ⟨_, slot, _, _⟩,
    count, step, _, within⟩ := valid
  have clampSteps : Lane.clamp 1 32 l.steps = l.steps := by unfold Lane.clamp; omega
  have clampDiv : Lane.clamp 1 96 l.div = l.div := by unfold Lane.clamp; omega
  have clampAmount : Lane.clamp 1 Notes.regLen l.rule.amount = l.rule.amount := by
    unfold Lane.clamp Notes.regLen at *; omega
  have mask : Lane.cleanMask l.mask = l.mask := by
    unfold Lane.cleanMask; rw [Nat.mod_eq_of_lt maskSmall]; simp [maskNe]
  have rhythm : Rhythm.make l.rhythm.kind l.rhythm.rotate l.rhythm.accents l.rhythm.rule l.rhythm.ratchet
      l.rhythm.subHits (min l.hits l.steps) l.steps l.rhythm.row = l.rhythm := by
    unfold Rhythm.make
    simp only [Nat.mod_eq_of_lt row, live, ite_false, Nat.min_eq_left hits]
    have k : min 3 l.rhythm.kind = l.rhythm.kind := Nat.min_eq_right kind
    have r : l.rhythm.rotate % l.steps = l.rhythm.rotate := Nat.mod_eq_of_lt rotate
    have a : min l.rhythm.accents l.hits = l.rhythm.accents := Nat.min_eq_left accents
    have u : l.rhythm.rule % 256 = l.rhythm.rule := Nat.mod_eq_of_lt rule
    have t : max 1 (min 4 l.rhythm.ratchet) = l.rhythm.ratchet := by omega
    have h : min l.rhythm.subHits (max 1 (min 4 l.rhythm.ratchet)) = l.rhythm.subHits := by omega
    rw [k, r, a, u, h, t]
  constructor
  · unfold Lane.reconfigure
    simp only [clampSteps, clampDiv, mask, ← gate, rhythm]
    rw [Nat.min_eq_left hits, Nat.mod_eq_of_lt count, Nat.mod_eq_of_lt step, Nat.min_eq_left within]
  · unfold Lane.setNotes
    simp only [clampAmount, Nat.min_eq_left prob, Nat.min_eq_left algoMax, Nat.min_eq_left mutateMax,
      Nat.mod_eq_of_lt slot, Nat.mod_eq_of_lt cursor]

/-- Changing the rhythm source keeps a consistent lane consistent, whatever numbers are given.
Why it matters: switching from Euclid to the automaton or the ratchet mid-song touches nothing but the
rhythm; counters, memory and the sounding note stay as they were. -/
theorem lane_set_rhythm_valid (l : Lane) (valid : Lane.Valid l) (kind rotate accents rule ratchet subHits : Nat)
    (reseed : Bool) : Lane.Valid (Lane.setRhythm l kind rotate accents rule ratchet subHits reseed) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := valid
  unfold Lane.setRhythm
  exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption, by assumption, by assumption,
    by assumption, by assumption, by assumption, by assumption, by assumption, by assumption, by assumption,
    by assumption, by assumption, by assumption, by assumption⟩

/-- A key the player presses keeps a consistent lane consistent.
Why it matters: playing along, or programming the step sequencer, can never break the lane. -/
theorem lane_learn_valid (l : Lane) (valid : Lane.Valid l) (note : Nat) : Lane.Valid (Lane.learn l note) := by
  have notesOk := notes_learn_keeps_valid l.rule l.span l.notes (note - l.low) valid.spanPositive valid.notesValid
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := valid
  unfold Lane.learn
  exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption, by assumption, by assumption,
    by assumption, by assumption, by assumption, by assumption, by assumption, by assumption, notesOk,
    by assumption, by assumption, by assumption, by assumption⟩
