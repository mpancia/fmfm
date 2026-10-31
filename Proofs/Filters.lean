import Firmware.Filters

/-- An `Int32` shifted right 8 places is its value divided by 256, rounded down. -/
private theorem filters_shift_eight (s : Int32) : (s >>> 8).toInt = s.toInt / 256 := by
  have : (s >>> 8).toInt = s.toInt >>> 8 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (8 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- One saw, as the top 13 bits of its phase, is between 0 and 8191. -/
private theorem filters_saw_bound (p : UInt32) :
    (p >>> 19).toInt32.toInt ≤ 8191 ∧ 0 ≤ (p >>> 19).toInt32.toInt := by
  have h : (p >>> 19).toNat < 2 ^ 13 := by
    rw [UInt32.toNat_shiftRight]
    have : (UInt32.toNat 19 % 32) = 19 := by decide
    rw [this, Nat.shiftRight_eq_div_pow]
    have := p.toNat_lt
    omega
  have e : (p >>> 19).toInt32.toInt = ((p >>> 19).toNat : Int) := by
    show (p >>> 19).toBitVec.toInt = _
    rw [BitVec.toInt_eq_toNat_of_lt]
    · simp
    · simp at h ⊢; omega
  omega

/-- The sum of the swarm's seven saws lies between -28672 and 28665, whatever the phases.
Why it matters: the sum is handed to the overdrive shaper offset by 32768 with no mask, so this is what keeps
that read inside the shaper's 257 entries (`tables_shape_reads_inside_257`). -/
theorem filters_swarm_sum_range (p0 p1 p2 p3 p4 p5 p6 : UInt32) :
    -28672 ≤ (Filters.swarmSum p0 p1 p2 p3 p4 p5 p6).toInt ∧
      (Filters.swarmSum p0 p1 p2 p3 p4 p5 p6).toInt ≤ 28665 := by
  unfold Filters.swarmSum
  have := filters_saw_bound p0; have := filters_saw_bound p1; have := filters_saw_bound p2
  have := filters_saw_bound p3; have := filters_saw_bound p4; have := filters_saw_bound p5
  have := filters_saw_bound p6
  simp only [Int32.toInt_add]
  simp [Int.bmod_def]
  omega

/-- A harmonic's amplitude moves toward its target and never passes it (shown for an amplitude below its
target; the other direction is symmetric), for values within a quarter of the 32-bit range.
Why it matters: when a harmonic is told to fade, it fades monotonically; it cannot overshoot and ring. -/
theorem filters_harmonic_glide_approaches (amplitude target : Int32)
    (lo : -1073741824 < amplitude.toInt) (hi : target.toInt ≤ 1073741824)
    (order : amplitude.toInt ≤ target.toInt) :
    amplitude.toInt ≤ (Filters.harmonicGlide amplitude target).toInt ∧
      (Filters.harmonicGlide amplitude target).toInt ≤ target.toInt := by
  unfold Filters.harmonicGlide
  have d : (target - amplitude).toInt = target.toInt - amplitude.toInt := by
    rw [Int32.toInt_sub]
    simp [Int.bmod_def]
    split <;> omega
  rw [Int32.toInt_add, filters_shift_eight, d]
  simp [Int.bmod_def]
  split <;> omega
