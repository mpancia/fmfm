import Spec.Euclid
import Firmware.Harmony

/-- The running total `step * hits / steps` goes up by 0 or 1 each step when `hits ≤ steps`. -/
private theorem euclid_total_steps_by_at_most_one (hits steps step : Nat) (positive : 0 < steps)
    (fits : hits ≤ steps) :
    step * hits / steps ≤ (step + 1) * hits / steps ∧
      (step + 1) * hits / steps ≤ step * hits / steps + 1 := by
  constructor
  · exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.le_succ _))
  · calc (step + 1) * hits / steps = (step * hits + hits) / steps := by rw [Nat.succ_mul]
      _ ≤ (step * hits + steps) / steps := Nat.div_le_div_right (by omega)
      _ = step * hits / steps + 1 := by rw [Nat.add_div_right _ positive]

/-- After `upTo` steps the hit count equals the running total `upTo * hits / steps`. -/
private theorem euclid_count_is_total (hits steps : Nat) (positive : 0 < steps) (fits : hits ≤ steps) :
    ∀ upTo, Euclid.countHits hits steps upTo = upTo * hits / steps := by
  intro upTo
  induction upTo with
  | zero => simp [Euclid.countHits]
  | succ upTo ih =>
    have ⟨low, high⟩ := euclid_total_steps_by_at_most_one hits steps upTo positive fits
    unfold Euclid.countHits Euclid.hit
    rw [ih]
    by_cases same : (upTo + 1) * hits / steps = upTo * hits / steps
    · simp [same]
    · simp only [bne_iff_ne, ne_eq, same, not_false_eq_true, ite_true]
      omega

/-- A bar of `steps` steps with `hits` hits (`hits ≤ steps`) plays exactly `hits` notes.
Why it matters: the pattern has the density you asked for, with no missing or extra notes. -/
theorem euclid_hit_count (hits steps : Nat) (positive : 0 < steps) (fits : hits ≤ steps) :
    Euclid.countHits hits steps steps = hits := by
  rw [euclid_count_is_total hits steps positive fits, Nat.mul_comm, Nat.mul_div_cancel _ positive]

/-- The last step of a bar is a hit whenever the bar has any hits.
Why it matters: the pattern always ends on a note, so the bar's last step (just before the circle comes round)
is where every Euclidean rhythm lands; the ratchet's first sub-hit relies on it too. -/
theorem euclid_last_step_hits (hits steps : Nat) (positive : 0 < hits) (fits : hits ≤ steps) :
    Euclid.hit hits steps (steps - 1) = true := by
  unfold Euclid.hit
  have stepsPos : 0 < steps := by omega
  have e : (steps - 1 + 1) * hits / steps = hits := by
    rw [Nat.sub_add_cancel stepsPos, Nat.mul_comm, Nat.mul_div_cancel _ stepsPos]
  have lt : (steps - 1) * hits / steps < hits := by
    rw [Nat.div_lt_iff_lt_mul stepsPos, Nat.mul_comm hits steps]
    exact Nat.mul_lt_mul_of_pos_right (by omega) positive
  simp only [bne_iff_ne, ne_eq, e]
  omega

/-- The hits in a window are the rise of the running total across it, for any window, past the bar included. -/
private theorem euclid_count_between_is_rise (hits steps start : Nat) (positive : 0 < steps)
    (fits : hits ≤ steps) : ∀ len, Euclid.countBetween hits steps start (start + len) =
      (start + len) * hits / steps - start * hits / steps := by
  intro len
  induction len with
  | zero => simp [Euclid.countBetween]
  | succ len ih =>
    have ⟨low, high⟩ := euclid_total_steps_by_at_most_one hits steps (start + len) positive fits
    have mono : start * hits / steps ≤ (start + len) * hits / steps :=
      Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))
    unfold Euclid.countBetween at *
    rw [show start + (len + 1) - start = len + 1 by omega, List.range_succ, List.filter_append,
      List.length_append, show start + len - start = len by omega] at *
    rw [ih, show start + (len + 1) = start + len + 1 by omega]
    unfold Euclid.hit
    by_cases same : (start + len + 1) * hits / steps = (start + len) * hits / steps
    · simp [same]
    · simp only [bne_iff_ne, ne_eq, same, not_false_eq_true, List.filter_cons, List.filter_nil, ite_true,
        List.length_singleton]
      omega

/-- The running total over a sum is the sum of the totals or one more. -/
private theorem euclid_floor_of_sum (a b steps : Nat) (positive : 0 < steps) :
    a / steps + b / steps ≤ (a + b) / steps ∧ (a + b) / steps ≤ a / steps + b / steps + 1 := by
  have ha := Nat.div_add_mod a steps
  have hb := Nat.div_add_mod b steps
  have ra := Nat.mod_lt a positive
  have rb := Nat.mod_lt b positive
  constructor
  · rw [Nat.le_div_iff_mul_le positive, Nat.add_mul, Nat.mul_comm (a / steps), Nat.mul_comm (b / steps)]
    omega
  · rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul positive,
      show (a / steps + b / steps + 1).succ = (a / steps + 1) + (b / steps + 1) by omega, Nat.add_mul,
      Nat.mul_comm (a / steps + 1), Nat.mul_comm (b / steps + 1), Nat.mul_succ, Nat.mul_succ]
    omega

/-- Every window of `len` steps of a bar of `steps` steps with `hits` hits plays `len * hits / steps` notes or
one more, wherever it starts, across the bar line included: the pattern is maximally even.
Why it matters: this is what "spread out" means and the reason the hits never bunch: 5 hits in 16 steps gives
every 4 steps one or two notes, every 8 steps two or three, and any two stretches of the same length are
within one note of each other. It is the Clough–Douthett maximal-evenness property of the floor-function
set, and the balance property of the Christoffel word, for the pattern the firmware plays. -/
theorem euclid_window_balanced (hits steps start len : Nat) (positive : 0 < steps) (fits : hits ≤ steps) :
    len * hits / steps ≤ Euclid.countBetween hits steps start (start + len) ∧
      Euclid.countBetween hits steps start (start + len) ≤ len * hits / steps + 1 := by
  rw [euclid_count_between_is_rise hits steps start positive fits len, Nat.add_mul]
  have ⟨low, high⟩ := euclid_floor_of_sum (start * hits) (len * hits) steps positive
  generalize (start * hits + len * hits) / steps = c at *
  generalize start * hits / steps = d at *
  generalize len * hits / steps = e at *
  omega

/-- Two windows of the same length never differ by more than one note: a direct form of the balance.
Why it matters: whichever two bars, half-bars or beats you compare, the Euclidean pattern gives them the same
number of notes or one apart; it has no busy and empty stretches. -/
theorem euclid_windows_within_one (hits steps a b len : Nat) (positive : 0 < steps) (fits : hits ≤ steps) :
    Euclid.countBetween hits steps a (a + len) ≤ Euclid.countBetween hits steps b (b + len) + 1 := by
  have ⟨_, ha⟩ := euclid_window_balanced hits steps a len positive fits
  have ⟨hb, _⟩ := euclid_window_balanced hits steps b len positive fits
  omega

/-- The firmware's pattern is the lower Christoffel word of slope `hits / steps` in Berstel's form: a step is a
hit exactly when the multiples of `hits` wrap round modulo `steps` there (for `hits < steps`; `hits = steps`
is every step).
Why it matters: it names what the sequencer plays: a Christoffel word, the discrete line from (0, 0) to
(steps, hits), the same object as the maximally even scales, so everything known about those words (they are
balanced, their conjugates are the Euclidean rhythms, their reversal is the upper word) is about these
rhythms. -/
theorem euclid_is_christoffel (hits steps k : Nat) (proper : hits < steps) :
    Euclid.hit hits steps k = Euclid.christoffel hits steps k := by
  unfold Euclid.hit Euclid.christoffel
  have positive : 0 < steps := by omega
  have ⟨low, high⟩ := euclid_total_steps_by_at_most_one hits steps k positive (by omega)
  have hk := Nat.div_add_mod (k * hits) steps
  have hk1 := Nat.div_add_mod ((k + 1) * hits) steps
  have rk := Nat.mod_lt (k * hits) positive
  have rk1 := Nat.mod_lt ((k + 1) * hits) positive
  generalize (k + 1) * hits / steps = q1 at *
  generalize k * hits / steps = q0 at *
  generalize (k + 1) * hits % steps = r1 at *
  generalize k * hits % steps = r0 at *
  rw [Nat.succ_mul] at hk1
  by_cases up : q1 = q0
  · subst up
    have : r1 = r0 + hits := by omega
    subst this
    simp
  · have : q1 = q0 + 1 := by omega
    subst this
    rw [Nat.mul_succ] at hk1
    have wraps : r1 < r0 := by omega
    have step : (q0 + 1 != q0) = true := by simp
    rw [step, decide_eq_true wraps]

/-- Bjorklund's algorithm, as Toussaint describes it, plays the firmware's pattern turned round: for every bar of
up to 32 steps and every number of hits, its output is `Euclid.hit` read from some step, checked case by case.
Why it matters: "Euclidean rhythm" usually means Bjorklund's output; the firmware plays the floor-function
form instead because a step is then one division, with no list to build. This says they are the same rhythm,
one rotation apart (the ROTATE knob reaches the rest), for every setting the knobs allow. -/
theorem euclid_bjorklund_is_rotation (steps : Nat) (positive : 0 < steps) (small : steps ≤ 32) (hits : Nat)
    (fits : hits ≤ steps) :
    ∃ rotation, rotation < steps ∧ Euclid.word hits steps rotation = Euclid.bjorklund hits steps := by
  have checked : ∀ steps : Fin 33, ∀ hits : Fin 33, 0 < steps.val → hits.val ≤ steps.val →
      (List.range steps.val).any
        (fun r => Euclid.word hits.val steps.val r == Euclid.bjorklund hits.val steps.val) = true := by
    decide +kernel
  have := checked ⟨steps, by omega⟩ ⟨hits, by omega⟩ positive fits
  obtain ⟨rotation, member, same⟩ := List.any_eq_true.mp this
  exact ⟨rotation, List.mem_range.mp member, beq_iff_eq.mp same⟩

/-- The major scale is the seven-hit Euclidean pattern on twelve steps, started on its sixth step; the major
pentatonic is the five-hit one started on its seventh (both as the SCALE table's masks).
Why it matters: the scales and the rhythms are one construction: the diatonic scale is the maximally even
seven of twelve (Clough and Douthett), so the SCALE knob and the HITS knob are reading the same word; a lane
set to seven hits in twelve steps taps out the major scale. -/
theorem euclid_major_scale_is_seven_of_twelve :
    Euclid.mask 7 6 = Harmony.scale 0 ∧ Euclid.mask 5 7 = Harmony.scale 2 := by
  decide +kernel
