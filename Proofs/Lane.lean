import Spec.Lane
import Proofs.Random
import Proofs.Quantizer

/-- Whatever settings are asked for, `make` gives a consistent lane.
Why it matters: bad numbers from the screen or a saved file cannot put a lane into a state the rest of the
code does not expect. -/
theorem lane_make_valid (hits steps div mask low span : Nat) (seed : UInt32) :
    Lane.Valid (Lane.make hits steps div mask low span seed) := by
  unfold Lane.make Lane.gateFor Lane.clamp
  by_cases empty : mask % 4096 = 0 <;> constructor <;> simp [empty] <;> omega

/-- `reconfigure` keeps a consistent lane consistent, even for nonsense settings.
Why it matters: turning a knob mid-song can never leave the lane with a position or timer out of range. -/
theorem lane_reconfigure_valid (l : Lane) (valid : Lane.Valid l) (hits steps div mask : Nat) :
    Lane.Valid (Lane.reconfigure l hits steps div mask) := by
  have fresh := lane_make_valid hits steps div mask l.low l.span l.rng
  have clampedLow : Lane.clamp 12 96 l.low = l.low := by
    have := valid.lowFloor; have := valid.lowCeiling
    simp only [Lane.clamp, Nat.min_eq_right this, Nat.max_eq_right valid.lowFloor]
  have clampedSpan : Lane.clamp 1 (120 - l.low) l.span = l.span := by
    have := valid.spanPositive; have := valid.spanFits
    simp only [Lane.clamp, Nat.min_eq_right (by omega : l.span ≤ 120 - l.low), Nat.max_eq_right valid.spanPositive]
  have low : (Lane.make hits steps div mask l.low l.span l.rng).low = l.low := by
    simp only [Lane.make, clampedLow]
  have span : (Lane.make hits steps div mask l.low l.span l.rng).span = l.span := by
    simp only [Lane.make, clampedLow, clampedSpan]
  unfold Lane.reconfigure
  generalize Lane.make hits steps div mask l.low l.span l.rng = f at *
  have timer := valid.soundingHasTimer
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := fresh
  rename_i gatePositive
  constructor <;> simp_all <;> first | omega | exact Nat.mod_lt _ (by omega)

/-- A tick keeps a consistent lane consistent.
Why it matters: however long the music runs, the counters stay in range and the sounding note and its timer
stay in step. -/
theorem lane_tick_valid (l : Lane) (valid : Lane.Valid l) : Lane.Valid (Lane.tick l) := by
  have timer := valid.soundingHasTimer
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := valid
  unfold Lane.tick Divider.tick
  by_cases wrap : l.count + 1 ≥ l.div <;> by_cases hit : Euclid.hit l.hits l.steps l.step = true <;>
    by_cases ending : l.gateLeft ≤ 1 <;> simp [wrap, hit, ending] <;> constructor <;> simp_all <;> first | omega | exact Nat.mod_lt _ (by omega)

/-- When a sounding note's gate runs out, the tick reports it as stopped.
Why it matters: no note stays on after its gate, so no stuck notes. -/
theorem lane_gate_end_stops_note (l : Lane) (note : Nat) (playing : l.playing = some note)
    (ending : l.gateLeft ≤ 1) : (Lane.tick l).off = some note := by
  unfold Lane.tick
  by_cases trigger : ((Divider.tick l.div l.count).2 && Euclid.hit l.hits l.steps l.step) = true <;>
    simp [trigger, ending, playing]

/-- A tick that starts a note also stops the one sounding before it.
Why it matters: a lane never has two notes on at once, so every note-on has exactly one note-off. -/
theorem lane_new_note_stops_old (l : Lane) (note : Nat) (starts : (Lane.tick l).on = some note) :
    (Lane.tick l).off = l.playing := by
  unfold Lane.tick at *
  by_cases trigger : ((Divider.tick l.div l.count).2 && Euclid.hit l.hits l.steps l.step) = true
  · simp [trigger]
  · by_cases ending : l.gateLeft ≤ 1 <;> simp [trigger, ending] at starts

/-- A note a tick starts is a valid MIDI note and is in the lane's scale.
Why it matters: the lane can never play a note the voices reject, or a note outside the key you chose. -/
theorem lane_note_in_scale (l : Lane) (valid : Lane.Valid l) (note : Nat)
    (starts : (Lane.tick l).on = some note) : note ≤ 127 ∧ Quantizer.inScale l.mask note = true := by
  unfold Lane.tick at starts
  by_cases trigger : ((Divider.tick l.div l.count).2 && Euclid.hit l.hits l.steps l.step) = true
  · simp only [trigger, ite_true, Option.some.injEq] at starts
    subst starts
    have spanSmall : l.span.toUInt32.toNat = l.span := by
      have := valid.spanFits; simp; omega
    have pick := random_below_lt l.rng l.span.toUInt32 (by rw [spanSmall]; exact valid.spanPositive)
      (by rw [spanSmall]; have := valid.spanFits; omega)
    rw [spanSmall] at pick
    have low := valid.lowFloor
    have fits := valid.spanFits
    have near := quantizer_snap_is_near l.mask (l.low + (Random.below l.rng l.span.toUInt32).toNat)
      valid.maskSmall valid.maskNotEmpty (by omega)
    exact ⟨by omega, quantizer_snap_in_scale _ _ valid.maskSmall valid.maskNotEmpty (by omega)⟩
  · by_cases ending : l.gateLeft ≤ 1 <;> simp [trigger, ending] at starts

/-- Silencing a consistent lane leaves it consistent.
Why it matters: stopping the clock cannot leave the lane with a timer and no note, or a note and no timer. -/
theorem lane_silence_valid (l : Lane) (valid : Lane.Valid l) : Lane.Valid l.silence := by
  have timer := valid.soundingHasTimer
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := valid
  unfold Lane.silence
  constructor <;> simp_all <;> omega

/-- Silencing reports the sounding note as stopped and leaves nothing sounding.
Why it matters: pressing stop never leaves a note hanging. -/
theorem lane_silence_stops_note (l : Lane) : l.silence.off = l.playing ∧ l.silence.playing = none := by
  simp [Lane.silence]
