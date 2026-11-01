import Firmware.Clock

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

/-- The clock accumulator never wraps: for a loop stall of up to 20 seconds, at any tempo up to 240 and under
HALF, straight or DOUBLE time, the 32-bit sum is the exact sum, starting from any residue below the longest
swung tick.
Why it matters: however long the main loop stalled (a patch load, a save, a screen redraw), the clock makes
up the time it missed rather than wrapping to garbage and jumping the song to a random place. -/
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

/-- Dividing the accumulator by the tick length is exactly the firmware's `while (acc >= len) { acc -= len;
tick(); }` loop: the ticks due times the length plus the remainder is the accumulator, and the remainder is
below one tick, so the loop stops.
Why it matters: the C clock keeps its loop; this says the loop and the division agree, so every fact
about `ticksDue` and `remainder` is a fact about the loop in `dinghy.c`. -/
theorem clock_division_is_the_loop (acc len : UInt32) (pos : 0 < len.toNat) :
    (Clock.ticksDue acc len).toNat * len.toNat + (Clock.remainder acc len).toNat = acc.toNat ∧
      (Clock.remainder acc len).toNat < len.toNat := by
  obtain ⟨d, r⟩ := clock_due_toNat acc len
  rw [d, r]
  exact ⟨by rw [Nat.mul_comm]; exact Nat.div_add_mod _ _, Nat.mod_lt _ pos⟩

/-- Over the same milliseconds from the same residue, HALF fires half the ticks of straight time, to within
the rounding of one tick: twice the HALF count is at most the straight count plus two, and the straight
count is at most twice the HALF count plus one (for straight ticks of 10000, swing 0).
Why it matters: HALF is exactly half speed, not roughly: a bar under HALF is two bars long to the tick, so the
chord changes, the lanes and the swing stay in step with each other and with where the song would be. -/
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

/-- Over the same milliseconds from the same residue, DOUBLE fires twice the ticks of straight time, to
within the rounding of one tick: the DOUBLE count is at most twice the straight count plus one, and twice
the straight count is at most the DOUBLE count plus two (for straight ticks of 10000, swing 0).
Why it matters: DOUBLE is exactly double speed: a bar under DOUBLE is half a bar long to the tick, so the
chord changes, the lanes and the swing stay in step with each other and with where the song would be. -/
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
