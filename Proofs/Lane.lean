import Spec.Lane
import Firmware.Patch
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

/-- `make` gives a valid lane for any settings.
Why it matters: out-of-range values from the screen or a saved file cannot produce an invalid lane. -/
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

/-- `reconfigure` keeps a valid lane valid for any settings.
Why it matters: turning a knob mid-song cannot push a position or timer out of range. -/
theorem lane_reconfigure_valid (l : Lane) (valid : Lane.Valid l) (hits steps div mask : Nat) :
    Lane.Valid (Lane.reconfigure l hits steps div mask) := by
  have timer := valid.soundingHasTimer
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := valid
  unfold Lane.reconfigure Lane.gateFor Lane.cleanMask Lane.clamp
  by_cases empty : mask % 4096 = 0 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp_all <;> first | omega | exact Nat.mod_lt _ (by omega)

/-- `setNotes` keeps a valid lane valid for any settings.
Why it matters: switching note algorithm mid-song cannot leave the loop position outside the loop. -/
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

/-- A tick keeps a valid lane valid.
Why it matters: counters, note memory and the sounding note stay consistent for any number of ticks. -/
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
Why it matters: no stuck notes. -/
theorem lane_gate_end_stops_note (l : Lane) (note : Nat) (playing : l.playing = some note)
    (ending : l.gateLeft ≤ 1) : (Lane.tick l).off = some note := by
  unfold Lane.tick
  split
  · simp [playing]
  · simp [playing]

/-- A tick that starts a note also stops the one sounding before it.
Why it matters: a lane never has two notes on at once. -/
theorem lane_new_note_stops_old (l : Lane) (note : Nat) (starts : (Lane.tick l).on = some note) :
    (Lane.tick l).off = l.playing := by
  unfold Lane.tick at *
  split at starts <;> split <;> first | rfl | (split at starts <;> simp_all)

/-- A note starts only on a step the rhythm marks as a hit (for a ratchet sub-hit, the step that just pulsed).
Why it matters: a rest never plays, regardless of note algorithm or play chance. -/
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

/-- A note a tick starts is at most 127 and is in the lane's scale.
Why it matters: the lane never plays a note the voices reject or one outside the chosen key. -/
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

/-- `silence` keeps a valid lane valid.
Why it matters: stopping the clock cannot leave a timer without a note or a note without a timer. -/
theorem lane_silence_valid (l : Lane) (valid : Lane.Valid l) : Lane.Valid l.silence := by
  have timer := valid.soundingHasTimer
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := valid
  unfold Lane.silence
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all <;> omega

/-- `silence` reports the sounding note as stopped and leaves nothing sounding.
Why it matters: stop never leaves a note hanging. -/
theorem lane_silence_stops_note (l : Lane) : l.silence.off = l.playing ∧ l.silence.playing = none := by
  simp [Lane.silence]

/-- Applying a lane's own settings back to it changes nothing, for a valid lane whose settings are within knob
range and whose gate is `gateFor div`. `make`, `reconfigure`, `setNotes` and `setRhythm` only produce such
lanes.
Why it matters: saving and reloading a patch, or redrawing a knob at its current value, does not change the
lane. -/
theorem lane_reconfigure_self (l : Lane) (valid : Lane.Valid l) (stepsMax : l.steps ≤ 32)
    (divMax : l.div ≤ 96) (algoMax : l.rule.algo ≤ 10) (mutateMax : l.rule.mutate ≤ 100) (gate : l.gate = Lane.gateFor l.div)
    (cursor : l.notes.cursor < l.rule.amount) (kind : l.rhythm.kind ≤ 3) (rotate : l.rhythm.rotate < l.steps)
    (accents : l.rhythm.accents ≤ l.hits) (rule : l.rhythm.rule < 256) (ratchet : 1 ≤ l.rhythm.ratchet ∧ l.rhythm.ratchet ≤ 4)
    (subHits : l.rhythm.subHits ≤ l.rhythm.ratchet) (row : Rhythm.cut l.steps l.rhythm.row = l.rhythm.row)
    (live : l.rhythm.row ≠ 0) :
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
    simp only [row, live, ite_false, Nat.min_eq_left hits]
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

/-- `setRhythm` keeps a valid lane valid for any settings.
Why it matters: switching rhythm source mid-song cannot break the lane. -/
theorem lane_set_rhythm_valid (l : Lane) (valid : Lane.Valid l) (kind rotate accents rule ratchet subHits : Nat)
    (reseed : Bool) : Lane.Valid (Lane.setRhythm l kind rotate accents rule ratchet subHits reseed) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := valid
  unfold Lane.setRhythm
  exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption, by assumption, by assumption,
    by assumption, by assumption, by assumption, by assumption, by assumption, by assumption, by assumption,
    by assumption, by assumption, by assumption, by assumption⟩

/-- `learn` (a key press) keeps a valid lane valid.
Why it matters: playing along or programming the step sequencer cannot break the lane. -/
theorem lane_learn_valid (l : Lane) (valid : Lane.Valid l) (note : Nat) : Lane.Valid (Lane.learn l note) := by
  have notesOk := notes_learn_keeps_valid l.rule l.span l.notes (note - l.low) valid.spanPositive valid.notesValid
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := valid
  unfold Lane.learn
  exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption, by assumption, by assumption,
    by assumption, by assumption, by assumption, by assumption, by assumption, by assumption, notesOk,
    by assumption, by assumption, by assumption, by assumption⟩

/-- A patch lane that fits (`PatchLane.Fits`) gives a lane with exactly the patch's rhythm settings: no clamp
in `Lane.make` or `Rhythm.make` changes a fitting value.
Why it matters: the FEEL settings a patch saves are the ones it plays back. -/
theorem lane_from_patch_keeps_feel (p : PatchLane) (fits : p.Fits) (div mask : Nat) (seed : UInt32) :
    let l := (Lane.make p.hits p.steps div mask p.low p.span seed).setRhythm p.feel p.rotate p.accents p.rule
      p.ratchet p.subHits true
    l.rhythm.kind = p.feel ∧ l.rhythm.rotate = p.rotate ∧ l.rhythm.accents = p.accents ∧
      l.rhythm.rule = p.rule ∧ l.rhythm.ratchet = p.ratchet ∧ l.rhythm.subHits = p.subHits ∧
      l.hits = p.hits ∧ l.steps = p.steps := by
  obtain ⟨hits, steps1, steps32, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, feel, rotate, accents, rule,
    ratchet1, ratchet4, sub1, subR⟩ := fits
  intro l
  have stepsEq : Lane.clamp 1 32 p.steps = p.steps := by unfold Lane.clamp; omega
  have mk : (Lane.make p.hits p.steps div mask p.low p.span seed).hits = p.hits ∧
      (Lane.make p.hits p.steps div mask p.low p.span seed).steps = p.steps := by
    unfold Lane.make
    simp only [stepsEq]
    exact ⟨Nat.min_eq_left hits, trivial⟩
  simp only [l, Lane.setRhythm, Rhythm.make, mk.1, mk.2]
  refine ⟨Nat.min_eq_right (by omega), Nat.mod_eq_of_lt rotate, Nat.min_eq_left accents, Nat.mod_eq_of_lt rule, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · trivial
  · trivial
