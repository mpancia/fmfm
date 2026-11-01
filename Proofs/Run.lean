import Spec.Run
import Spec.Euclid
import Spec.Rhythm
import Proofs.Rhythm
import Proofs.Lane
import Proofs.Euclid

/-- Moving the clock on does not touch the sounding note. -/
private theorem run_moved_playing (l : Lane) : l.moved.playing = l.playing := rfl

/-- One tick: the notes it starts and stops account exactly for the change in what is sounding. -/
private theorem run_tick_balance (l : Lane) :
    (if l.tick.on.isSome then 1 else 0) + l.soundingCount =
      (if l.tick.off.isSome then 1 else 0) + l.tick.soundingCount := by
  unfold Lane.soundingCount Lane.tick
  cases h : l.playing <;> split <;> (try split) <;> simp [run_moved_playing, h]

/-- Setting changes keep the sounding note. -/
private theorem run_settings_keep_sounding (l : Lane) (op : Lane.Op) (notTick : op ≠ .tick) :
    (l.apply op).playing = l.playing := by
  cases op with
  | tick => exact absurd rfl notTick
  | reconfigure h s d m => rfl
  | setNotes a p n m => rfl
  | setRhythm k r a u t s re => rfl
  | learn n => rfl

/-- On-count and off-count of a trace, one pair at a time. -/
private theorem run_counts_cons (x : Option Nat × Option Nat) (t : List (Option Nat × Option Nat)) :
    Lane.noteOns (x :: t) = (if x.2.isSome then 1 else 0) + Lane.noteOns t ∧
      Lane.noteOffs (x :: t) = (if x.1.isSome then 1 else 0) + Lane.noteOffs t := by
  unfold Lane.noteOns Lane.noteOffs
  constructor <;> simp [List.filter_cons] <;> split <;> simp <;> omega

/-- Over any run, note-ons plus what was sounding at the start equal note-offs plus what sounds at the end. -/
private theorem run_balance (ops : List Lane.Op) : ∀ l : Lane,
    Lane.noteOns (l.trace ops) + l.soundingCount =
      Lane.noteOffs (l.trace ops) + (l.run ops).soundingCount := by
  induction ops with
  | nil => intro l; simp [Lane.trace, Lane.run, Lane.noteOns, Lane.noteOffs]
  | cons op rest ih =>
    intro l
    cases op with
    | tick =>
      have step := run_tick_balance l
      have later := ih l.tick
      have ⟨ons, offs⟩ := run_counts_cons (l.tick.off, l.tick.on) (l.tick.trace rest)
      simp only [Lane.trace, Lane.run, Lane.apply] at *
      omega
    | reconfigure h s d m =>
      have keep := run_settings_keep_sounding l (.reconfigure h s d m) (by simp)
      simp only [Lane.trace, Lane.run]
      rw [show l.soundingCount = (l.apply (.reconfigure h s d m)).soundingCount by
        simp [Lane.soundingCount, keep]]
      exact ih _
    | setNotes a p n m =>
      have keep := run_settings_keep_sounding l (.setNotes a p n m) (by simp)
      simp only [Lane.trace, Lane.run]
      rw [show l.soundingCount = (l.apply (.setNotes a p n m)).soundingCount by
        simp [Lane.soundingCount, keep]]
      exact ih _
    | setRhythm k r a u t s re =>
      have keep := run_settings_keep_sounding l (.setRhythm k r a u t s re) (by simp)
      simp only [Lane.trace, Lane.run]
      rw [show l.soundingCount = (l.apply (.setRhythm k r a u t s re)).soundingCount by
        simp [Lane.soundingCount, keep]]
      exact ih _
    | learn n =>
      have keep := run_settings_keep_sounding l (.learn n) (by simp)
      simp only [Lane.trace, Lane.run]
      rw [show l.soundingCount = (l.apply (.learn n)).soundingCount by
        simp [Lane.soundingCount, keep]]
      exact ih _

/-- Every note a lane starts during a run is stopped: after any sequence of ticks and setting changes, the
number of note-ons equals the number of note-offs plus the one note still sounding, which stopping the clock
then reports as stopped (`lane_silence_stops_note`) and leaves nothing sounding.
Why it matters: this is the no-stuck-notes promise for a whole performance, not one tick: however long you
play and whatever you turn, pressing stop leaves nothing sounding and nothing unaccounted for. -/
theorem run_every_note_on_has_a_note_off (l : Lane) (fresh : l.playing = none) (ops : List Lane.Op) :
    Lane.noteOns (l.trace ops) = Lane.noteOffs (l.trace ops) + (l.run ops).soundingCount ∧
      (l.run ops).silence.playing = none := by
  have balance := run_balance ops l
  have start : l.soundingCount = 0 := by simp [Lane.soundingCount, fresh]
  exact ⟨by omega, rfl⟩

/-- Counting one more: `n = d * q + r` with `r < d` becomes `(n + 1) % d` and `(n + 1) / d`. -/
private theorem run_count_succ (d q r : Nat) (dPos : 0 < d) (rBelow : r < d) :
    (d * q + r + 1) % d = (if r + 1 = d then 0 else r + 1) ∧
      (d * q + r + 1) / d = (if r + 1 = d then q + 1 else q) := by
  rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mul_add_div dPos]
  split
  · rename_i full; rw [full, Nat.mod_self, Nat.div_self dPos]; simp
  · rename_i part
    have : r + 1 < d := by omega
    rw [Nat.mod_eq_of_lt this, Nat.div_eq_of_lt this]; simp

/-- One tick moves the clock exactly as the counting says: if the count was `n % div` and the step
`(n / div) % steps`, afterwards they are the same for `n + 1`. The settings do not change. -/
private theorem run_tick_clock (l : Lane) (n : Nat) (divPos : 0 < l.div)
    (count : l.count = n % l.div) (step : l.step = (n / l.div) % l.steps) :
    l.tick.count = (n + 1) % l.div ∧ l.tick.step = ((n + 1) / l.div) % l.steps ∧
      l.tick.div = l.div ∧ l.tick.steps = l.steps := by
  have moved : l.tick.count = l.moved.count ∧ l.tick.step = l.moved.step ∧ l.tick.div = l.div ∧
      l.tick.steps = l.steps := by
    unfold Lane.tick; split <;> (try split) <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have decomp : n = l.div * (n / l.div) + n % l.div := (Nat.div_add_mod n l.div).symm
  have ⟨nextMod, nextDiv⟩ := run_count_succ l.div (n / l.div) (n % l.div) divPos (Nat.mod_lt _ divPos)
  rw [← decomp] at nextMod nextDiv
  have rBelow := Nat.mod_lt n divPos
  generalize n % l.div = r at *
  generalize n / l.div = q at *
  refine ⟨?_, ?_, moved.2.2.1, moved.2.2.2⟩
  · rw [moved.1, nextMod]; unfold Lane.moved Divider.tick; dsimp only; rw [count]
    by_cases full : r + 1 = l.div
    · rw [ite_eq_left (by omega), ite_eq_left full]
    · rw [ite_eq_right (by omega), ite_eq_right full]
  · rw [moved.2.1, nextDiv]; unfold Lane.moved Lane.atStep Divider.tick; dsimp only; rw [count, step]
    by_cases full : r + 1 = l.div
    · rw [ite_eq_left full, ite_eq_left (show r + 1 ≥ l.div by omega)]; simp [Nat.add_mod]
    · rw [ite_eq_right full, ite_eq_right (show ¬ (r + 1 ≥ l.div) by omega)]; simp

/-- After `n` ticks from a fresh lane, the clock stands at `(n / div) % steps`, whatever notes played.
Why it matters: the step position depends only on the tick count, so four lanes at different speeds stay in
phase forever: nothing a note does can make a lane drift. -/
theorem run_clock_never_drifts (hits steps div mask low span : Nat) (seed : UInt32) (n : Nat) :
    let l := Lane.make hits steps div mask low span seed
    (l.run (List.replicate n .tick)).step = Lane.stepAfter l.div l.steps n ∧
      (l.run (List.replicate n .tick)).count = n % l.div := by
  intro l
  have valid := lane_make_valid hits steps div mask low span seed
  have divPos : 0 < l.div := valid.divPositive
  have fresh : l.count = 0 ∧ l.step = 0 := ⟨rfl, rfl⟩
  suffices h : ∀ k (m : Lane), m.div = l.div → m.steps = l.steps → m.count = k % l.div →
      m.step = (k / l.div) % l.steps →
      (m.run (List.replicate n .tick)).step = ((k + n) / l.div) % l.steps ∧
        (m.run (List.replicate n .tick)).count = (k + n) % l.div ∧
        (m.run (List.replicate n .tick)).div = l.div by
    have := h 0 l rfl rfl (by simp [fresh]) (by simp [fresh])
    simp only [Nat.zero_add] at this
    exact ⟨this.1, this.2.1⟩
  clear fresh
  induction n with
  | zero => intro k m hd hs hc hst; simp [Lane.run, hc, hst, hd]
  | succ n ih =>
    intro k m hd hs hc hst
    have t := run_tick_clock m k (hd ▸ divPos) (by rw [hc, hd]) (by rw [hst, hd, hs])
    have later := ih (k + 1) m.tick (t.2.2.1.trans hd) (t.2.2.2.trans hs) (by rw [t.1, hd])
      (by rw [t.2.1, hd, hs])
    simp only [List.replicate_succ, Lane.run, Lane.apply]
    rw [show k + (n + 1) = k + 1 + n by omega]
    exact later

/-- A steady lane: no ratchet, a play chance of 100, and a rhythm whose hits are `f`. -/
private def Lane.Steady (l : Lane) (f : Nat → Bool) : Prop :=
  l.rhythm.kind ≠ 3 ∧ l.prob = 100 ∧ ∀ s, Rhythm.hit l.rhythm l.hits l.steps s = f s

/-- Whether tick `n` of a steady lane plays: it is the pulse of its step and that step is a hit. -/
private def run_plays (f : Nat → Bool) (steps div n : Nat) : Bool :=
  decide ((n + 1) % div = 0) && f ((n / div) % steps)

/-- How many of the ticks `k` to `k + count - 1` play. -/
private def run_ons (f : Nat → Bool) (steps div k : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => (if run_plays f steps div k then 1 else 0) + run_ons f steps div (k + 1) count

/-- Hits among the first `s` steps, step by step. -/
private def run_count (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | s + 1 => run_count f s + if f s then 1 else 0

/-- The step-by-step count is `Rhythm.count`. -/
private theorem run_count_eq (f : Nat → Bool) : ∀ s, run_count f s = Rhythm.count f s := by
  intro s
  induction s with
  | zero => rfl
  | succ s ih =>
    unfold run_count Rhythm.count
    rw [ih, List.range_succ, List.filter_append, List.length_append]
    unfold Rhythm.count
    simp only [List.filter_cons, List.filter_nil]
    cases f s <;> simp

/-- A lane whose clock stands at tick `n` is on its step's pulse exactly when the tick count says so. -/
private theorem run_pulse (l : Lane) (n : Nat) (divPos : 0 < l.div) (count : l.count = n % l.div) :
    l.atStep = decide ((n + 1) % l.div = 0) := by
  unfold Lane.atStep Divider.tick
  rw [count]
  have rBelow := Nat.mod_lt n divPos
  have next : (n + 1) % l.div = if n % l.div + 1 = l.div then 0 else n % l.div + 1 := by
    have decomp : n + 1 = l.div * (n / l.div) + n % l.div + 1 := by
      have := Nat.div_add_mod n l.div; omega
    rw [decomp]; exact (run_count_succ l.div (n / l.div) (n % l.div) divPos rBelow).1
  rw [next]
  by_cases full : n % l.div + 1 = l.div
  · rw [ite_eq_left (by omega), ite_eq_left full]; simp
  · rw [ite_eq_right (by omega), ite_eq_right full]; simp

/-- A steady lane whose clock stands at tick `n` starts a note on this tick exactly when `run_plays` says. -/
private theorem run_steady_tick_on (l : Lane) (f : Nat → Bool) (n : Nat) (steady : l.Steady f)
    (divPos : 0 < l.div) (count : l.count = n % l.div) (step : l.step = (n / l.div) % l.steps) :
    l.tick.on.isSome = run_plays f l.steps l.div n := by
  have chance : Lane.draw (Random.next (Random.next (Random.next l.rng))) 100 < l.prob := by
    rw [steady.2.1]
    exact random_below_lt _ 100 (by decide) (by decide)
  have plays : l.plays = l.isHit := by
    unfold Lane.plays; simp [chance]
  have pulse := run_pulse l n divPos count
  have sub : l.subHit = if (n + 1) % l.div = 0 then some 0 else none := by
    unfold Lane.subHit; rw [ite_eq_right steady.1, pulse]; simp
  have hitStep : l.hitStep = l.step := by
    unfold Lane.hitStep; rw [sub]; split
    · rename_i heq; split at heq <;> simp at heq
    · rfl
  have hit : l.isHit = run_plays f l.steps l.div n := by
    unfold Lane.isHit run_plays
    rw [sub, hitStep, step, steady.2.2]
    unfold Rhythm.subPlays
    by_cases p : (n + 1) % l.div = 0 <;> simp [p]
  have on : l.tick.on.isSome = l.plays := by
    unfold Lane.tick; split <;> (try split) <;> simp_all
  rw [on, plays, hit]

/-- A tick keeps the kind, the chance, the hits and the steps; it keeps the rhythm itself unless the bar ends
(when an automaton's row moves on). -/
private theorem run_tick_steady (l : Lane) :
    l.tick.rhythm.kind = l.rhythm.kind ∧ l.tick.prob = l.prob ∧ l.tick.hits = l.hits ∧ l.tick.steps =
        l.steps ∧
      (l.atBarEnd = false → l.tick.rhythm = l.rhythm) := by
  have m : l.tick.rhythm = l.moved.rhythm ∧ l.tick.prob = l.prob ∧ l.tick.hits = l.hits ∧ l.tick.steps =
      l.steps := by
    unfold Lane.tick; split <;> (try split) <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have endKind : ∀ r steps, (Rhythm.endBar r steps).kind = r.kind := by
    intro r steps; unfold Rhythm.endBar; split <;> rfl
  refine ⟨?_, m.2.1, m.2.2.1, m.2.2.2, ?_⟩
  · rw [m.1]; unfold Lane.moved; dsimp only; split
    · exact endKind _ _
    · rfl
  · intro notEnd; rw [m.1]; unfold Lane.moved; dsimp only; rw [notEnd]; rfl

/-- Before the last tick of the bar, the bar does not end. -/
private theorem run_not_bar_end (l : Lane) (k : Nat) (divPos : 0 < l.div) (count : l.count = k % l.div)
    (step : l.step = (k / l.div) % l.steps) (inside : k + 1 < l.steps * l.div) : l.atBarEnd = false := by
  unfold Lane.atBarEnd
  rw [run_pulse l k divPos count, step]
  have stepsPos : 0 < l.steps := by
    rcases Nat.eq_zero_or_pos l.steps with z | p
    · rw [z] at inside; omega
    · exact p
  have quotBelow : k / l.div < l.steps := by
    rw [Nat.div_lt_iff_lt_mul divPos]; omega
  rw [Nat.mod_eq_of_lt quotBelow]
  by_cases pulse : (k + 1) % l.div = 0
  · by_cases last : k / l.div + 1 = l.steps
    · exfalso
      have decomp := Nat.div_add_mod k l.div
      have remBelow := Nat.mod_lt k divPos
      have full : k % l.div + 1 = l.div := by
        have : (l.div * (k / l.div) + k % l.div + 1) % l.div = 0 := by rw [decomp]; exact pulse
        rw [(run_count_succ l.div (k / l.div) (k % l.div) divPos remBelow).1] at this
        split at this <;> omega
      have : l.steps * l.div = l.div * (k / l.div) + l.div := by
        rw [← last, Nat.mul_comm, Nat.mul_succ]
      omega
    · simp [last]
  · simp [pulse]

/-- The note-ons of a run of ticks inside one bar of a steady lane are the ticks `run_plays` says play. -/
private theorem run_steady_ons (f : Nat → Bool) (n : Nat) : ∀ (k : Nat) (m : Lane), (0 < n → m.Steady f) →
    0 < m.div → m.count = k % m.div → m.step = (k / m.div) % m.steps → k + n ≤ m.steps * m.div →
    Lane.noteOns (m.trace (List.replicate n .tick)) = run_ons f m.steps m.div k n := by
  induction n with
  | zero => intro k m _ _ _ _ _; simp [Lane.trace, Lane.noteOns, run_ons]
  | succ n ih =>
    intro k m steadyIf divPos count step inside
    have steady := steadyIf (by omega)
    have t := run_tick_clock m k divPos count step
    have on := run_steady_tick_on m f k steady divPos count step
    have keep := run_tick_steady m
    have steadyNext : 0 < n → m.tick.Steady f := by
      intro pos
      have same := keep.2.2.2.2 (run_not_bar_end m k divPos count step (by omega))
      refine ⟨by rw [keep.1]; exact steady.1, by rw [keep.2.1]; exact steady.2.1, ?_⟩
      intro s; rw [same, keep.2.2.1, keep.2.2.2.1]; exact steady.2.2 s
    have later := ih (k + 1) m.tick steadyNext (t.2.2.1 ▸ divPos) (by rw [t.1, t.2.2.1])
      (by rw [t.2.1, t.2.2.1, t.2.2.2]) (by rw [t.2.2.1, t.2.2.2]; omega)
    have ⟨ons, _⟩ := run_counts_cons (m.tick.off, m.tick.on) (m.tick.trace (List.replicate n .tick))
    rw [List.replicate_succ]
    show Lane.noteOns ((m.tick.off, m.tick.on) :: m.tick.trace (List.replicate n .tick)) = _
    rw [ons, later, t.2.2.1, t.2.2.2]
    show (if m.tick.on.isSome = true then 1 else 0) + _ = _
    rw [on]
    rfl

/-- Counting over two stretches of ticks is counting over each. -/
private theorem run_ons_add (f : Nat → Bool) (steps div : Nat) (a : Nat) : ∀ (k b : Nat),
    run_ons f steps div k (a + b) = run_ons f steps div k a + run_ons f steps div (k + a) b := by
  induction a with
  | zero => intro k b; simp [run_ons]
  | succ a ih =>
    intro k b
    rw [show k + (a + 1) = k + 1 + a by omega, show a + 1 + b = (a + b) + 1 by omega]
    show (if run_plays f steps div k then 1 else 0) + run_ons f steps div (k + 1) (a + b) =
      (if run_plays f steps div k then 1 else 0) + run_ons f steps div (k + 1) a + run_ons f steps div
          (k + 1 + a) b
    rw [ih (k + 1) b]; omega

/-- Of the `div` ticks of step `s` (ticks `s * div` on), exactly the last one is a pulse,
    and it plays when the
step is a hit. -/
private theorem run_ons_step (f : Nat → Bool) (steps div s : Nat) (divPos : 0 < div) (inBar : s < steps) :
    run_ons f steps div (s * div) div = if f s then 1 else 0 := by
  suffices h : ∀ r, r ≤ div →
      run_ons f steps div (s * div + (div - r)) r = if r = 0 then 0 else if f s then 1 else 0 by
    have := h div (Nat.le_refl _)
    rw [Nat.sub_self, Nat.add_zero] at this
    rw [this, ite_eq_right (by omega)]
  intro r
  induction r with
  | zero => intro _; simp [run_ons]
  | succ r ih =>
    intro le
    unfold run_ons run_plays
    have offset : s * div + (div - (r + 1)) = div * s + (div - (r + 1)) := by rw [Nat.mul_comm]
    have below : div - (r + 1) < div := by omega
    have quot : (div * s + (div - (r + 1))) / div = s := by
      rw [Nat.mul_add_div divPos, Nat.div_eq_of_lt below]; simp
    have stepMod : s % steps = s := Nat.mod_eq_of_lt inBar
    have pulse : (div * s + (div - (r + 1)) + 1) % div = 0 ↔ r = 0 := by
      rw [Nat.add_assoc, Nat.mul_add_mod]
      constructor
      · intro h
        have : div - (r + 1) + 1 < div ∨ div - (r + 1) + 1 = div := by omega
        rcases this with lt | eq
        · rw [Nat.mod_eq_of_lt lt] at h; omega
        · omega
      · intro h; subst h; rw [show div - (0 + 1) + 1 = div by omega, Nat.mod_self]
    rw [offset, quot, stepMod]
    have next : div * s + (div - (r + 1)) + 1 = s * div + (div - r) := by rw [Nat.mul_comm]; omega
    by_cases z : r = 0
    · subst z
      have p : (div * s + (div - (0 + 1)) + 1) % div = 0 := pulse.mpr rfl
      rw [decide_eq_true p, Bool.true_and, next, ih (by omega)]
      simp
    · have np : ¬ (div * s + (div - (r + 1)) + 1) % div = 0 := fun h => z (pulse.mp h)
      rw [decide_eq_false np, Bool.false_and, next, ih (by omega)]
      simp [z]

/-- Over the first `s` steps of a bar, the ticks that play are the hits among those steps. -/
private theorem run_ons_steps (f : Nat → Bool) (steps div : Nat) (divPos : 0 < div) : ∀ s, s ≤ steps →
    run_ons f steps div 0 (s * div) = run_count f s := by
  intro s
  induction s with
  | zero => intro _; simp [run_ons, run_count]
  | succ s ih =>
    intro le
    rw [Nat.succ_mul, run_ons_add, Nat.zero_add, ih (by omega), run_ons_step f steps div s divPos (by omega)]
    rfl

/-- One bar of a steady lane from its first tick: the note-ons are the rhythm's hits over the bar. -/
private theorem run_bar_steady (l : Lane) (f : Nat → Bool) (steady : l.Steady f) (divPos : 0 < l.div)
    (fresh : l.count = 0 ∧ l.step = 0) :
    Lane.noteOns (l.trace (List.replicate (l.steps * l.div) .tick)) = Rhythm.count f l.steps := by
  rw [run_steady_ons f (l.steps * l.div) 0 l (fun _ => steady) divPos (by simp [fresh.1]) (by simp [fresh.2])
    (by omega), run_ons_steps f l.steps l.div divPos l.steps (Nat.le_refl _), run_count_eq]

/-- A lane with the Euclidean, turned or automaton rhythm (any kind but the ratchet) and a play chance of 100
plays, over the `steps * div` ticks of a bar from a fresh lane, exactly the hits its rhythm marks in that bar:
for the automaton, the ones of its row at the start of the bar.
Why it matters: `run_bar_plays_every_hit` for every rhythm the knobs offer except ratchets: whatever the
FEEL page is set to, the bar plays what the screen's row of hits shows, no note missing and none added;
and for the automaton it says the row you see is the bar you hear, before it moves a generation on. -/
theorem run_bar_plays_the_rhythm (hits steps div mask low span : Nat) (seed : UInt32)
    (kind rotate accents rule ratchet subHits : Nat) (noRatchet : kind < 3) :
    let l := ((Lane.make hits steps div mask low span seed).setNotes 0 100 1 0).setRhythm
      kind rotate accents rule ratchet subHits true
    Lane.noteOns (l.trace (List.replicate (l.steps * l.div) .tick)) =
      Rhythm.count (Rhythm.hit l.rhythm l.hits l.steps) l.steps := by
  intro l
  have valid := lane_set_rhythm_valid _ (lane_set_notes_valid (Lane.make hits steps div mask low span seed)
    (lane_make_valid hits steps div mask low span seed) 0 100 1 0) kind rotate accents rule ratchet subHits
    true
  have steady : l.Steady (Rhythm.hit l.rhythm l.hits l.steps) := by
    refine ⟨?_, ?_, fun _ => rfl⟩
    · show (Rhythm.make kind rotate accents rule ratchet subHits _ _ _).kind ≠ 3
      simp [Rhythm.make]; omega
    · rfl
  exact run_bar_steady l _ steady valid.divPositive ⟨rfl, rfl⟩

/-- A plain lane (the Euclidean source, play chance 100) plays exactly `hits` notes in a bar: over the
`steps * div` ticks of a bar from a fresh lane, the trace has `hits` note-ons, for any settings at all (`make`
holds them to what the knobs can produce).
Why it matters: the safety theorems say a lane never plays on a rest; this one says it does play on every
hit. The bar has the density the HITS knob asks for, no note missing: the machine makes the music it
promises, not merely nothing wrong. -/
theorem run_bar_plays_every_hit (hits steps div mask low span : Nat) (seed : UInt32) :
    let l := (Lane.make hits steps div mask low span seed).setNotes 0 100 1 0
    Lane.noteOns (l.trace (List.replicate (l.steps * l.div) .tick)) = l.hits := by
  intro l
  have valid := lane_set_notes_valid (Lane.make hits steps div mask low span seed)
    (lane_make_valid hits steps div mask low span seed) 0 100 1 0
  have steady : l.Steady (Euclid.hit l.hits l.steps) := by
    refine ⟨?_, rfl, ?_⟩
    · show (Rhythm.make 0 0 0 90 1 1 _ _ 0).kind ≠ 3
      simp [Rhythm.make]
    · intro s
      show Rhythm.hit (Rhythm.make 0 0 0 90 1 1 _ _ 0) l.hits l.steps s = _
      simp [Rhythm.hit, Rhythm.source, Rhythm.make]
  rw [run_bar_steady l _ steady valid.divPositive ⟨rfl, rfl⟩, ← run_count_eq]
  have same : ∀ s, run_count (Euclid.hit l.hits l.steps) s = Euclid.countHits l.hits l.steps s := by
    intro s; induction s with
    | zero => rfl
    | succ s ih => unfold run_count Euclid.countHits; rw [ih]
  rw [same]
  exact euclid_hit_count l.hits l.steps valid.stepsPositive valid.hitsFit

/-- A turned lane (the Euclidean source rotated by ROTATE, play chance 100) plays exactly `hits` notes in a
bar too.
Why it matters: turning the pattern moves the hits round the bar without losing or doubling one; a lane
with ROTATE set plays the density the HITS knob asks for. -/
theorem run_bar_plays_every_hit_turned (hits steps div mask low span : Nat) (seed : UInt32)
    (rotate accents rule ratchet subHits : Nat) :
    let l := ((Lane.make hits steps div mask low span seed).setNotes 0 100 1 0).setRhythm
      1 rotate accents rule ratchet subHits true
    Lane.noteOns (l.trace (List.replicate (l.steps * l.div) .tick)) = l.hits := by
  intro l
  have valid := lane_set_rhythm_valid _ (lane_set_notes_valid (Lane.make hits steps div mask low span seed)
    (lane_make_valid hits steps div mask low span seed) 0 100 1 0) 1 rotate accents rule ratchet subHits true
  rw [run_bar_plays_the_rhythm hits steps div mask low span seed 1 rotate accents rule ratchet subHits
      (by decide)]
  have kind : l.rhythm.kind = 1 := by
    show (Rhythm.make 1 rotate accents rule ratchet subHits _ _ _).kind = 1
    simp [Rhythm.make]
  rw [rhythm_rotate_keeps_hits l.rhythm l.hits l.steps kind valid.stepsPositive, ← run_count_eq]
  have same : ∀ s, run_count (Euclid.hit l.hits l.steps) s = Euclid.countHits l.hits l.steps s := by
    intro s; induction s with
    | zero => rfl
    | succ s ih => unfold run_count Euclid.countHits; rw [ih]
  rw [same]
  exact euclid_hit_count l.hits l.steps valid.stepsPositive valid.hitsFit

/-- A ratchet lane: its rhythm is `r`, a ratchet (kind 3), and its play chance is 100. -/
private def Lane.Ratchet (l : Lane) (r : Rhythm) : Prop := l.rhythm = r ∧ l.prob = 100 ∧ r.kind = 3

/-- Whether tick `n` of a ratchet lane plays: the tick starts sub-hit `k` (the pulse of its step when `k = 0`;
otherwise `k * div / ratchet` ticks after the pulse of the step before, which the step counter has left
behind) of a step the rhythm marks, and sub-hit `k` plays. -/
private def run_sub_plays (r : Rhythm) (hits steps div n : Nat) : Bool :=
  match Rhythm.subIndex div r.ratchet ((n + 1) % div) with
  | none => false
  | some k =>
    Rhythm.hit r hits steps (if k = 0 then (n / div) % steps else ((n / div) % steps + steps - 1) % steps) &&
      Rhythm.subPlays r k

/-- How many of the ticks `k` to `k + count - 1` of a ratchet lane play. -/
private def run_sub_ons (r : Rhythm) (hits steps div k : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 =>
    (if run_sub_plays r hits steps div k then 1 else 0) + run_sub_ons r hits steps div (k + 1) count

/-- A ratchet lane whose clock stands at tick `n` starts a note on this tick exactly when `run_sub_plays`
says. -/
private theorem run_ratchet_tick_on (l : Lane) (r : Rhythm) (n : Nat) (ratchet : l.Ratchet r)
    (count : l.count = n % l.div) (step : l.step = (n / l.div) % l.steps) :
    l.tick.on.isSome = run_sub_plays r l.hits l.steps l.div n := by
  have chance : Lane.draw (Random.next (Random.next (Random.next l.rng))) 100 < l.prob := by
    rw [ratchet.2.1]
    exact random_below_lt _ 100 (by decide) (by decide)
  have plays : l.plays = l.isHit := by
    unfold Lane.plays; simp [chance]
  have on : l.tick.on.isSome = l.plays := by
    unfold Lane.tick; split <;> (try split) <;> simp_all
  have sub : l.subHit = Rhythm.subIndex l.div r.ratchet ((n + 1) % l.div) := by
    unfold Lane.subHit; rw [ratchet.1, ite_eq_left ratchet.2.2, count, Nat.mod_add_mod]
  rw [on, plays]
  unfold Lane.isHit Lane.hitStep run_sub_plays
  rw [sub, ratchet.1, step]
  cases Rhythm.subIndex l.div r.ratchet ((n + 1) % l.div) with
  | none => rfl
  | some k =>
    cases k with
    | zero => rfl
    | succ k => rfl

/-- The note-ons of a run of ticks inside one bar of a ratchet lane are the ticks `run_sub_plays` says
play. -/
private theorem run_ratchet_ons (r : Rhythm) (n : Nat) : ∀ (k : Nat) (m : Lane), (0 < n → m.Ratchet r) →
    0 < m.div → m.count = k % m.div → m.step = (k / m.div) % m.steps → k + n ≤ m.steps * m.div →
    Lane.noteOns (m.trace (List.replicate n .tick)) = run_sub_ons r m.hits m.steps m.div k n := by
  induction n with
  | zero => intro k m _ _ _ _ _; simp [Lane.trace, Lane.noteOns, run_sub_ons]
  | succ n ih =>
    intro k m ratchetIf divPos count step inside
    have ratchet := ratchetIf (by omega)
    have t := run_tick_clock m k divPos count step
    have on := run_ratchet_tick_on m r k ratchet count step
    have keep := run_tick_steady m
    have ratchetNext : 0 < n → m.tick.Ratchet r := by
      intro pos
      have same := keep.2.2.2.2 (run_not_bar_end m k divPos count step (by omega))
      exact ⟨same.trans ratchet.1, keep.2.1.trans ratchet.2.1, ratchet.2.2⟩
    have later := ih (k + 1) m.tick ratchetNext (t.2.2.1 ▸ divPos) (by rw [t.1, t.2.2.1])
      (by rw [t.2.1, t.2.2.1, t.2.2.2]) (by rw [t.2.2.1, t.2.2.2]; omega)
    have ⟨ons, _⟩ := run_counts_cons (m.tick.off, m.tick.on) (m.tick.trace (List.replicate n .tick))
    rw [List.replicate_succ]
    show Lane.noteOns ((m.tick.off, m.tick.on) :: m.tick.trace (List.replicate n .tick)) = _
    rw [ons, later, keep.2.2.1, t.2.2.1, t.2.2.2]
    show (if m.tick.on.isSome = true then 1 else 0) + _ = _
    rw [on]
    rfl

/-- `find?` over `range' s n` finds nothing when nothing in the range satisfies `p`. -/
private theorem run_find_none (p : Nat → Bool) : ∀ (n s : Nat), (∀ j, s ≤ j → j < s + n → p j = false) →
    (List.range' s n).find? p = none := by
  intro n
  induction n with
  | zero => intro s _; rfl
  | succ n ih =>
    intro s none
    rw [List.range'_succ, List.find?_cons, none s (Nat.le_refl _) (by omega)]
    exact ih (s + 1) (fun j le lt => none j (by omega) (by omega))

/-- `find?` over `range' s n` finds `m` when `m` is in the range and satisfies `p` and nothing before it
does. -/
private theorem run_find_some (p : Nat → Bool) : ∀ (n s m : Nat), s ≤ m → m < s + n → p m = true →
    (∀ j, s ≤ j → j < m → p j = false) → (List.range' s n).find? p = some m := by
  intro n
  induction n with
  | zero => intro s m le lt; omega
  | succ n ih =>
    intro s m le lt pm before
    rw [List.range'_succ, List.find?_cons]
    by_cases e : s = m
    · subst e; rw [pm]
    · rw [before s (Nat.le_refl _) (by omega)]
      exact ih (s + 1) m (by omega) (by omega) pm (fun j le lt => before j (by omega) lt)

/-- Sub-hit offsets `k * div / ratchet` never go down with `k`. -/
private theorem run_offset_le (div ratchet i j : Nat) (le : i ≤ j) : i * div / ratchet ≤ j * div / ratchet :=
  Nat.div_le_div_right (Nat.mul_le_mul_right div le)

/-- With the ratchet at most `div`, sub-hit offsets `k * div / ratchet` go strictly up with `k`. -/
private theorem run_offset_lt (div ratchet : Nat) (fits : ratchet ≤ div) (ratchetPos : 0 < ratchet)
    (i j : Nat) (lt : i < j) : i * div / ratchet < j * div / ratchet := by
  have next : i * div / ratchet + 1 ≤ (i + 1) * div / ratchet := by
    rw [Nat.le_div_iff_mul_le ratchetPos, Nat.add_mul, Nat.one_mul, Nat.add_mul, Nat.one_mul]
    have := Nat.div_mul_le_self (i * div) ratchet
    omega
  have := run_offset_le div ratchet (i + 1) j lt
  omega

/-- Count 0 of a step (the pulse) starts sub-hit 0. -/
private theorem run_sub_index_pulse (div ratchet : Nat) (ratchetPos : 0 < ratchet) :
    Rhythm.subIndex div ratchet 0 = some 0 := by
  unfold Rhythm.subIndex
  rw [List.range_eq_range']
  exact run_find_some _ ratchet 0 0 (Nat.le_refl _) (by omega) (by simp) (fun j _ lt => by omega)

/-- Count `(k + 1) * div / ratchet` starts sub-hit `k + 1`, the ratchet being at most `div`. -/
private theorem run_sub_index_hit (div ratchet k : Nat) (fits : ratchet ≤ div) (below : k + 1 < ratchet) :
    Rhythm.subIndex div ratchet ((k + 1) * div / ratchet) = some (k + 1) := by
  unfold Rhythm.subIndex
  rw [List.range_eq_range']
  refine run_find_some _ ratchet 0 (k + 1) (by omega) (by omega) (by simp) ?_
  intro j _ lt
  have := run_offset_lt div ratchet fits (by omega) j (k + 1) lt
  simp; omega

/-- A count strictly between the offsets of sub-hits `k` and `k + 1` starts no sub-hit. -/
private theorem run_sub_index_none (div ratchet k c : Nat) (after : k * div / ratchet < c)
    (before : c < (k + 1) * div / ratchet) :
    Rhythm.subIndex div ratchet c = none := by
  unfold Rhythm.subIndex
  rw [List.range_eq_range']
  apply run_find_none
  intro j _ lt
  simp
  rcases Nat.lt_or_ge j (k + 1) with low | high
  · have := run_offset_le div ratchet j k (by omega); omega
  · have := run_offset_le div ratchet (k + 1) j high; omega

/-- Tick `o` of step `s`'s block (its ticks from `s * div`) as `run_sub_plays` sees it: the count after it is
`o + 1` (0 at the step's end) and the step counter stands at `s`. -/
private theorem run_sub_plays_at (r : Rhythm) (hits steps div s o : Nat) (divPos : 0 < div)
    (inBar : s < steps) (inStep : o < div) :
    run_sub_plays r hits steps div (s * div + o) =
      match Rhythm.subIndex div r.ratchet (if o + 1 = div then 0 else o + 1) with
      | none => false
      | some k =>
        Rhythm.hit r hits steps (if k = 0 then s else (s + steps - 1) % steps) && Rhythm.subPlays r k := by
  unfold run_sub_plays
  have next := (run_count_succ div s o divPos inStep).1
  rw [Nat.mul_comm] at next
  have quot : (s * div + o) / div = s := by
    rw [Nat.mul_comm, Nat.mul_add_div divPos, Nat.div_eq_of_lt inStep, Nat.add_zero]
  rw [next, quot, Nat.mod_eq_of_lt inBar]

/-- Counting over two stretches of ticks is counting over each. -/
private theorem run_sub_ons_add (r : Rhythm) (hits steps div : Nat) (a : Nat) : ∀ (k b : Nat),
    run_sub_ons r hits steps div k (a + b) =
      run_sub_ons r hits steps div k a + run_sub_ons r hits steps div (k + a) b := by
  induction a with
  | zero => intro k b; simp [run_sub_ons]
  | succ a ih =>
    intro k b
    rw [show k + (a + 1) = k + 1 + a by omega, show a + 1 + b = (a + b) + 1 by omega]
    show (if run_sub_plays r hits steps div k then 1 else 0) + run_sub_ons r hits steps div (k + 1) (a + b) =
      (if run_sub_plays r hits steps div k then 1 else 0) + run_sub_ons r hits steps div (k + 1) a +
        run_sub_ons r hits steps div (k + 1 + a) b
    rw [ih (k + 1) b]; omega

/-- Chunk `k` of step `s`'s block: its ticks from offset `k * div / ratchet` up to the next sub-hit's offset.
Only its last tick plays: the pulse of step `s` for the last chunk, sub-hit `k + 1` of the step before for the
others. -/
private theorem run_sub_ons_chunk (r : Rhythm) (hits steps div s k : Nat) (divPos : 0 < div)
    (inBar : s < steps) (fits : r.ratchet ≤ div) (below : k < r.ratchet) :
    run_sub_ons r hits steps div (s * div + k * div / r.ratchet)
        ((k + 1) * div / r.ratchet - k * div / r.ratchet) =
      if k + 1 = r.ratchet then (if Rhythm.hit r hits steps s then 1 else 0)
      else if Rhythm.hit r hits steps ((s + steps - 1) % steps) && Rhythm.subPlays r (k + 1) then 1
      else 0 := by
  have ratchetPos : 0 < r.ratchet := by omega
  have mono := run_offset_lt div r.ratchet fits ratchetPos k (k + 1) (Nat.lt_succ_self k)
  have top : (k + 1) * div / r.ratchet ≤ div := by
    have := run_offset_le div r.ratchet (k + 1) r.ratchet below
    rw [Nat.mul_div_cancel_left div ratchetPos] at this
    exact this
  have full : (k + 1) * div / r.ratchet = div ↔ k + 1 = r.ratchet := by
    constructor
    · intro e
      rcases Nat.lt_or_ge (k + 1) r.ratchet with lt | ge
      · have := run_offset_lt div r.ratchet fits ratchetPos (k + 1) r.ratchet lt
        rw [Nat.mul_div_cancel_left div ratchetPos] at this
        omega
      · omega
    · intro e; rw [e, Nat.mul_div_cancel_left div ratchetPos]
  have hit : k + 1 < r.ratchet → Rhythm.subIndex div r.ratchet ((k + 1) * div / r.ratchet) = some (k + 1) :=
    run_sub_index_hit div r.ratchet k fits
  have none : ∀ c, k * div / r.ratchet < c → c < (k + 1) * div / r.ratchet →
      Rhythm.subIndex div r.ratchet c = none := run_sub_index_none div r.ratchet k
  generalize ha : k * div / r.ratchet = a at *
  generalize hb : (k + 1) * div / r.ratchet = b at *
  suffices h : ∀ m, m ≤ b - a → run_sub_ons r hits steps div (s * div + (b - m)) m =
      if m = 0 then 0 else
      if k + 1 = r.ratchet then (if Rhythm.hit r hits steps s then 1 else 0)
      else if Rhythm.hit r hits steps ((s + steps - 1) % steps) && Rhythm.subPlays r (k + 1) then 1 else 0 by
    have := h (b - a) (Nat.le_refl _)
    rw [show b - (b - a) = a by omega, ite_eq_right (by omega)] at this
    exact this
  intro m
  induction m with
  | zero => intro _; simp [run_sub_ons]
  | succ m ih =>
    intro le
    unfold run_sub_ons
    rw [run_sub_plays_at r hits steps div s (b - (m + 1)) divPos inBar (by omega),
      show s * div + (b - (m + 1)) + 1 = s * div + (b - m) by omega, ih (by omega)]
    by_cases z : m = 0
    · subst z
      by_cases e : b = div
      · rw [ite_eq_left (show b - (0 + 1) + 1 = div by omega), run_sub_index_pulse div r.ratchet ratchetPos,
          ite_eq_left (full.mp e)]
        simp [Rhythm.subPlays]
      · have notLast : ¬ k + 1 = r.ratchet := fun c => e (full.mpr c)
        rw [ite_eq_right (show ¬ b - (0 + 1) + 1 = div by omega), show b - (0 + 1) + 1 = b by omega,
          hit (by omega), ite_eq_right notLast]
        simp
    · rw [ite_eq_right (show ¬ b - (m + 1) + 1 = div by omega), none (b - (m + 1) + 1) (by omega) (by omega)]
      simp [z]

/-- The first `j` chunks of step `s`'s block (its ticks up to offset `j * div / ratchet`), `j` below the
ratchet: the sub-hits `1` to `j` of the step before that play, when that step is a hit. -/
private theorem run_sub_ons_chunks (r : Rhythm) (hits steps div s : Nat) (divPos : 0 < div)
    (inBar : s < steps) (fits : r.ratchet ≤ div) : ∀ j, j < r.ratchet →
    run_sub_ons r hits steps div (s * div) (j * div / r.ratchet) =
      if Rhythm.hit r hits steps ((s + steps - 1) % steps) then
        run_count (fun k => Rhythm.subPlays r (k + 1)) j
      else 0 := by
  intro j
  induction j with
  | zero => intro _; simp [run_sub_ons, run_count]
  | succ j ih =>
    intro below
    have mono := run_offset_lt div r.ratchet fits (by omega) j (j + 1) (Nat.lt_succ_self j)
    rw [show (j + 1) * div / r.ratchet =
          j * div / r.ratchet + ((j + 1) * div / r.ratchet - j * div / r.ratchet)
        by omega,
      run_sub_ons_add, ih (by omega), run_sub_ons_chunk r hits steps div s j divPos inBar fits (by omega),
      ite_eq_right (show ¬ j + 1 = r.ratchet by omega)]
    simp only [run_count]
    by_cases h1 : Rhythm.hit r hits steps ((s + steps - 1) % steps) = true <;>
      by_cases h2 : Rhythm.subPlays r (j + 1) = true <;> simp [h1, h2]

/-- Step `s`'s block (its `div` ticks from `s * div`): the pulse of step `s` when it is a hit, and the
sub-hits `1` to `ratchet - 1` of the step before that play, when that one is a hit. -/
private theorem run_sub_ons_block (r : Rhythm) (hits steps div s : Nat) (divPos : 0 < div) (inBar : s < steps)
    (fits : r.ratchet ≤ div) (ratchetPos : 0 < r.ratchet) :
    run_sub_ons r hits steps div (s * div) div =
      (if Rhythm.hit r hits steps s then 1 else 0) +
        if Rhythm.hit r hits steps ((s + steps - 1) % steps) then
          run_count (fun k => Rhythm.subPlays r (k + 1)) (r.ratchet - 1) else 0 := by
  have last := run_sub_ons_chunk r hits steps div s (r.ratchet - 1) divPos inBar fits (by omega)
  rw [show r.ratchet - 1 + 1 = r.ratchet by omega, Nat.mul_div_cancel_left div ratchetPos, ite_eq_left rfl]
    at last
  have mono := run_offset_le div r.ratchet (r.ratchet - 1) r.ratchet (by omega)
  rw [Nat.mul_div_cancel_left div ratchetPos] at mono
  have split : run_sub_ons r hits steps div (s * div) div = run_sub_ons r hits steps div (s * div)
      ((r.ratchet - 1) * div / r.ratchet + (div - (r.ratchet - 1) * div / r.ratchet)) := by
    congr 1; omega
  rw [split, run_sub_ons_add,
    run_sub_ons_chunks r hits steps div s divPos inBar fits (r.ratchet - 1) (by omega), last]
  omega

/-- Over the first `s` steps of a bar: the hits among them, and for each hit among the steps before each of
them the sub-hits `1` to `ratchet - 1` that play. -/
private theorem run_sub_ons_blocks (r : Rhythm) (hits steps div : Nat) (divPos : 0 < div)
    (fits : r.ratchet ≤ div) (ratchetPos : 0 < r.ratchet) : ∀ s, s ≤ steps →
    run_sub_ons r hits steps div 0 (s * div) =
      run_count (Rhythm.hit r hits steps) s + run_count (fun k => Rhythm.subPlays r (k + 1)) (r.ratchet - 1) *
        run_count (fun i => Rhythm.hit r hits steps ((i + steps - 1) % steps)) s := by
  intro s
  induction s with
  | zero => intro _; simp [run_sub_ons, run_count]
  | succ s ih =>
    intro le
    rw [Nat.succ_mul, run_sub_ons_add, Nat.zero_add, ih (by omega),
      run_sub_ons_block r hits steps div s divPos (by omega) fits ratchetPos]
    generalize run_count (fun k => Rhythm.subPlays r (k + 1)) (r.ratchet - 1) = c
    simp only [run_count]
    by_cases h1 : Rhythm.hit r hits steps s = true <;>
      by_cases h2 : Rhythm.hit r hits steps ((s + steps - 1) % steps) = true <;>
      simp [h1, h2, Nat.mul_add] <;> omega

/-- Counting a property of the step before each step of a bar counts it over the bar. -/
private theorem run_count_turned (f : Nat → Bool) (steps : Nat) (stepsPos : 0 < steps) :
    run_count (fun i => f ((i + steps - 1) % steps)) steps = run_count f steps := by
  have shift : ∀ s, s < steps → run_count (fun i => f ((i + steps - 1) % steps)) (s + 1) =
      (if f (steps - 1) then 1 else 0) + run_count f s := by
    intro s
    induction s with
    | zero =>
      intro _
      simp [run_count, Nat.mod_eq_of_lt (show steps - 1 < steps by omega)]
    | succ s ih =>
      intro lt
      show run_count (fun i => f ((i + steps - 1) % steps)) (s + 1) +
        (if f ((s + 1 + steps - 1) % steps) then 1 else 0) = _
      rw [ih (by omega), show s + 1 + steps - 1 = s + steps by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show s < steps by omega)]
      show _ = _ + (run_count f s + if f s then 1 else 0)
      omega
  cases steps with
  | zero => omega
  | succ t =>
    rw [shift t (Nat.lt_succ_self t)]
    show _ = run_count f t + if f t then 1 else 0
    rw [Nat.add_sub_cancel]
    omega

/-- Counting over `m + 1` is the first and then the rest, counted from 1. -/
private theorem run_count_shift (f : Nat → Bool) : ∀ m,
    run_count f (m + 1) = (if f 0 then 1 else 0) + run_count (fun k => f (k + 1)) m := by
  intro m
  induction m with
  | zero => simp [run_count]
  | succ m ih =>
    show run_count f (m + 1) + (if f (m + 1) then 1 else 0) =
      _ + (run_count (fun k => f (k + 1)) m + if f (m + 1) then 1 else 0)
    rw [ih]; omega

/-- A ratchet lane (kind 3, play chance 100) whose ratchet is at most `div` plays, over the `steps * div`
ticks of a bar from a fresh lane, exactly `hits` times the number of sub-hits that play: every hit step
rolls the same sub-hits (its pulse and those SUB-HITS spreads over the ratchet), each on a tick of its own.
The bound `ratchet ≤ div` is what keeps the sub-hits on distinct ticks; a step shorter than its ratchet
merges them.
Why it matters: ratchets play exactly the rolls the knobs ask for, no sub-hit lost or doubled; with this
every rhythm kind the FEEL page offers has its liveness theorem. -/
theorem run_bar_plays_every_ratchet (hits steps div mask low span : Nat) (seed : UInt32)
    (rotate accents rule ratchet subHits : Nat) :
    let l := ((Lane.make hits steps div mask low span seed).setNotes 0 100 1 0).setRhythm
      3 rotate accents rule ratchet subHits true
    l.rhythm.ratchet ≤ l.div →
    Lane.noteOns (l.trace (List.replicate (l.steps * l.div) .tick)) =
      l.hits * Rhythm.count (Rhythm.subPlays l.rhythm) l.rhythm.ratchet := by
  intro l fits
  have valid := lane_set_rhythm_valid _ (lane_set_notes_valid (Lane.make hits steps div mask low span seed)
    (lane_make_valid hits steps div mask low span seed) 0 100 1 0) 3 rotate accents rule ratchet subHits true
  have kind : l.rhythm.kind = 3 := by
    show (Rhythm.make 3 rotate accents rule ratchet subHits _ _ _).kind = 3
    simp [Rhythm.make]
  have ratchetPos : 0 < l.rhythm.ratchet := by
    show 0 < (Rhythm.make 3 rotate accents rule ratchet subHits _ _ _).ratchet
    simp [Rhythm.make]; omega
  have hitEq : Rhythm.hit l.rhythm l.hits l.steps = Euclid.hit l.hits l.steps := by
    funext s; unfold Rhythm.hit Rhythm.source; simp [kind]
  rw [run_ratchet_ons l.rhythm (l.steps * l.div) 0 l (fun _ => ⟨rfl, rfl, kind⟩) valid.divPositive
      (by rw [Nat.zero_mod]; rfl) (by rw [Nat.zero_div, Nat.zero_mod]; rfl) (by omega),
    run_sub_ons_blocks l.rhythm l.hits l.steps l.div valid.divPositive fits ratchetPos l.steps
      (Nat.le_refl _),
    hitEq, run_count_turned _ _ valid.stepsPositive]
  have same : ∀ s, run_count (Euclid.hit l.hits l.steps) s = Euclid.countHits l.hits l.steps s := by
    intro s; induction s with
    | zero => rfl
    | succ s ih => unfold run_count Euclid.countHits; rw [ih]
  rw [same, euclid_hit_count l.hits l.steps valid.stepsPositive valid.hitsFit, ← run_count_eq]
  have first : Rhythm.subPlays l.rhythm 0 = true := by simp [Rhythm.subPlays]
  have count := run_count_shift (Rhythm.subPlays l.rhythm) (l.rhythm.ratchet - 1)
  rw [show l.rhythm.ratchet - 1 + 1 = l.rhythm.ratchet by omega, first, ite_eq_left rfl] at count
  rw [count]
  generalize run_count (fun k => Rhythm.subPlays l.rhythm (k + 1)) (l.rhythm.ratchet - 1) = c
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm c]
