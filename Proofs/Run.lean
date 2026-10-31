import Spec.Run
import Proofs.Lane

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
