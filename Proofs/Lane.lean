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
  notes_choose_stays_in_range l.rule l.span l.notes _ _ _
    (by have := valid.spanPositive; omega) valid.loopLengthPositive valid.loopLengthFits valid.notesValid
    (lane_draw_below _ _ (by have := valid.spanPositive; omega) (by have := valid.spanFits; omega))

/-- A tick keeps a consistent lane consistent.
Why it matters: however long the music runs, the counters stay in range, the note memory stays sound, and the
sounding note and its timer stay in step. -/
theorem lane_tick_valid (l : Lane) (valid : Lane.Valid l) : Lane.Valid (Lane.tick l) := by
  have ⟨countOk, stepOk, divSame, stepsSame⟩ := lane_moved_counters l valid
  have ⟨_, choiceOk⟩ := lane_pick_ok l valid
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

/-- A note starts only on a step the rhythm marks as a hit.
Why it matters: the Euclidean pattern is respected; a rest never plays, whatever the note algorithm or the
play chance say. -/
theorem lane_note_only_on_hit (l : Lane) (note : Nat) (starts : (Lane.tick l).on = some note) :
    Euclid.hit l.hits l.steps l.step = true := by
  have plays : l.plays = true → Euclid.hit l.hits l.steps l.step = true := by
    intro h
    unfold Lane.plays Lane.isHit at h
    simp only [Bool.and_eq_true] at h
    exact h.1.2
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
