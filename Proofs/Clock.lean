import Firmware.Clock
import Spec.Clock

/-- The accumulator and the tempo product as plain numbers: nothing wraps when the accumulator is below one
longest tick, the gap is under 20 seconds, the tempo is at most 240 and the punch scale at most 200. -/
private theorem clock_advance_toNat (acc dt bpm tempo : UInt32) (accSmall : acc.toNat < 16666 + 1)
    (gap : dt.toNat ≤ 20000) (bpmIn : bpm.toNat ≤ 240) (tempoIn : tempo.toNat ≤ 200) :
    (Clock.advance acc dt bpm tempo).toNat = acc.toNat + dt.toNat * bpm.toNat * 4 * tempo.toNat / 100 := by
  unfold Clock.advance
  have b : dt.toNat * bpm.toNat ≤ 20000 * 240 := Nat.mul_le_mul gap bpmIn
  have t : dt.toNat * bpm.toNat * 4 * tempo.toNat ≤ 20000 * 240 * 4 * 200 :=
    Nat.mul_le_mul (Nat.mul_le_mul b (Nat.le_refl 4)) tempoIn
  simp only [UInt32.toNat_add, UInt32.toNat_div, UInt32.toNat_mul, UInt32.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (by omega : dt.toNat * bpm.toNat < 4294967296),
    Nat.mod_eq_of_lt (by omega : dt.toNat * bpm.toNat * 4 < 4294967296),
    Nat.mod_eq_of_lt (by omega : dt.toNat * bpm.toNat * 4 * tempo.toNat < 4294967296),
    Nat.mod_eq_of_lt (by omega)]

/-- The clock accumulator never wraps: for a stall of up to 20 s, tempo up to 240 and a tempo factor up to 200
percent, starting from any residue below the longest swung tick, the 32-bit sum is the exact sum.
Why it matters: after a long main-loop stall (patch load, save, redraw) the clock makes up the missed time
instead of jumping the song. -/
theorem clock_advance_never_wraps (acc dt bpm tempo : UInt32) (accSmall : acc.toNat < 16666 + 1)
    (gap : dt.toNat ≤ 20000) (bpmIn : bpm.toNat ≤ 240) (tempoIn : tempo.toNat ≤ 200) :
    (Clock.advance acc dt bpm tempo).toNat = acc.toNat + dt.toNat * bpm.toNat * 4 * tempo.toNat / 100 :=
  clock_advance_toNat acc dt bpm tempo accSmall gap bpmIn tempoIn

/-- The ticks due and the remainder as plain numbers. -/
private theorem clock_due_toNat (acc len : UInt32) :
    (Clock.ticksDue acc len).toNat = acc.toNat / len.toNat ∧
      (Clock.remainder acc len).toNat = acc.toNat % len.toNat := by
  unfold Clock.ticksDue Clock.remainder
  simp only [UInt32.toNat_div, UInt32.toNat_mod, and_self]

/-- `ticksDue` and `remainder` describe the firmware's `while (acc >= len) { acc -= len; tick(); }` loop:
ticks due times the length plus the remainder is the accumulator, and the remainder is below one tick.
Why it matters: every fact about `ticksDue` and `remainder` is a fact about the loop in `dinghy.c`. -/
theorem clock_division_is_the_loop (acc len : UInt32) (pos : 0 < len.toNat) :
    (Clock.ticksDue acc len).toNat * len.toNat + (Clock.remainder acc len).toNat = acc.toNat ∧
      (Clock.remainder acc len).toNat < len.toNat := by
  obtain ⟨d, r⟩ := clock_due_toNat acc len
  rw [d, r]
  exact ⟨by rw [Nat.mul_comm]; exact Nat.div_add_mod _ _, Nat.mod_lt _ pos⟩

/-- Over the same milliseconds from the same residue, HALF fires half the ticks of straight time to within one
tick of rounding: `2 * half ≤ straight + 2` and `straight ≤ 2 * half + 1` (straight ticks of 10000, swing 0).
Why it matters: a bar under HALF is two bars long to the tick, so lanes, swing and chord changes stay in
step. -/
theorem clock_half_time_is_half (acc dt bpm : UInt32) (accSmall : acc.toNat < 16666 + 1)
    (gap : dt.toNat ≤ 20000) (bpmIn : bpm.toNat ≤ 240) :
    (Clock.ticksDue (Clock.advance acc dt bpm 50) 10000).toNat * 2 ≤
        (Clock.ticksDue (Clock.advance acc dt bpm 100) 10000).toNat + 2 ∧
      (Clock.ticksDue (Clock.advance acc dt bpm 100) 10000).toNat ≤
        (Clock.ticksDue (Clock.advance acc dt bpm 50) 10000).toNat * 2 + 1 := by
  rw [(clock_due_toNat _ _).1, (clock_due_toNat _ _).1,
    clock_advance_toNat acc dt bpm 50 accSmall gap bpmIn (by decide),
    clock_advance_toNat acc dt bpm 100 accSmall gap bpmIn (by decide)]
  simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- Over the same milliseconds from the same residue, DOUBLE fires twice the ticks of straight time to within
one tick of rounding: `double ≤ 2 * straight + 1` and `2 * straight ≤ double + 2` (straight ticks of 10000,
swing 0).
Why it matters: a bar under DOUBLE is half a bar long to the tick, so lanes, swing and chord changes stay in
step. -/
theorem clock_double_time_is_double (acc dt bpm : UInt32) (accSmall : acc.toNat < 16666 + 1)
    (gap : dt.toNat ≤ 20000) (bpmIn : bpm.toNat ≤ 240) :
    (Clock.ticksDue (Clock.advance acc dt bpm 200) 10000).toNat ≤
        (Clock.ticksDue (Clock.advance acc dt bpm 100) 10000).toNat * 2 + 1 ∧
      (Clock.ticksDue (Clock.advance acc dt bpm 100) 10000).toNat * 2 ≤
        (Clock.ticksDue (Clock.advance acc dt bpm 200) 10000).toNat + 2 := by
  rw [(clock_due_toNat _ _).1, (clock_due_toNat _ _).1,
    clock_advance_toNat acc dt bpm 200 accSmall gap bpmIn (by decide),
    clock_advance_toNat acc dt bpm 100 accSmall gap bpmIn (by decide)]
  simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

/-- Taking the whole ticks out first and then counting over the rest is counting over the whole. -/
private theorem clock_loop_split (a x : Nat) : a / 10000 + (a % 10000 + x) / 10000 = (a + x) / 10000 := by
  have := Nat.div_add_mod a 10000
  rw [show a + x = 10000 * (a / 10000) + (a % 10000 + x) by omega, Nat.mul_add_div (by decide)]

/-- The loop from any residue below one tick: its ticks are the residue plus the elapsed time's worth of
tick, in whole ticks. -/
private theorem clock_loop_from (bpm : UInt32) (bpmIn : bpm.toNat ≤ 240) : ∀ (gaps : List UInt32),
    (∀ dt ∈ gaps, dt.toNat ≤ 20000) → ∀ acc : UInt32, acc.toNat < 10000 →
    Clock.loop bpm 100 10000 acc gaps =
      List.replicate ((acc.toNat + Clock.elapsed gaps * bpm.toNat * 4) / 10000) .tick := by
  intro gaps
  induction gaps with
  | nil =>
    intro _ acc small
    simp [Clock.loop, Clock.elapsed, Nat.div_eq_of_lt small]
  | cons dt gaps ih =>
    intro short acc small
    have advance := clock_advance_toNat acc dt bpm 100 (by omega) (short dt (List.mem_cons_self ..)) bpmIn
      (by decide)
    have ⟨due, rest⟩ := clock_due_toNat (Clock.advance acc dt bpm 100) 10000
    simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.mul_div_cancel _ (by decide : 0 < 100)]
      at advance due rest
    have later := ih (fun g mem => short g (List.mem_cons_of_mem dt mem)) (Clock.remainder _ 10000)
      (by rw [rest]; exact Nat.mod_lt _ (by decide))
    rw [Clock.loop, later, List.replicate_append_replicate, due, rest, advance, clock_loop_split]
    congr 2
    simp only [Clock.elapsed, List.map_cons, List.sum_cons, Nat.add_mul]
    omega

/-- Straight time at full tempo: over any run of main-loop passes whose gaps are each under 20 s and add up to
`ms` milliseconds, at a tempo of at most 240, the loop from an empty accumulator feeds the lanes exactly
`ms * bpm * 4 / 10000` ticks, whatever the gaps are.
Why it matters: the song follows elapsed time, not how often the main loop gets round to polling, so a slow
redraw or a patch load leaves the tempo alone. -/
theorem clock_loop_follows_the_wall_clock (bpm : UInt32) (gaps : List UInt32) (bpmIn : bpm.toNat ≤ 240)
    (gapsShort : ∀ dt ∈ gaps, dt.toNat ≤ 20000) :
    Clock.loop bpm 100 10000 0 gaps = List.replicate (Clock.elapsed gaps * bpm.toNat * 4 / 10000) .tick := by
  have := clock_loop_from bpm bpmIn gaps gapsShort 0 (by decide)
  simpa using this
