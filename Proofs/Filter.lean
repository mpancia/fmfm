import Firmware.FilterApi

/-! The per-voice filter (`Firmware/Filter.lean`): fully open with no resonance it is the identity, so every
sound with the default settings is what it was; the states and nodes are held to ±65536 and with them every
product and sum of a sample fits in 32 bits, so the arithmetic is exact (no wrap) and the output is bounded;
the coefficient tables are in range and the cutoff sweep rises; a settled constant is a fixed point (the
low-pass passes it, the band and high outputs are zero), and with the band node at rest a low-pass step moves
from the state toward the input and never past it. -/

/-- An arithmetic shift right of a 32-bit number by 1 is division by 2, rounding down. -/
private theorem filter_shift1 (x : Int32) : (x >>> 1).toInt = x.toInt / 2 := by
  show (x >>> 1).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by 13. -/
private theorem filter_shift13 (x : Int32) : (x >>> 13).toInt = x.toInt / 8192 := by
  show (x >>> 13).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by 14. -/
private theorem filter_shift14 (x : Int32) : (x >>> 14).toInt = x.toInt / 16384 := by
  show (x >>> 14).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by 15. -/
private theorem filter_shift15 (x : Int32) : (x >>> 15).toInt = x.toInt / 32768 := by
  show (x >>> 15).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- A product that fits in 32 bits is exact. -/
private theorem filter_mul_exact (a b : Int32) (fits : (a.toInt * b.toInt).natAbs < 2 ^ 31) :
    (a * b).toInt = a.toInt * b.toInt := by
  rw [Int32.toInt_mul]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A sum that fits in 32 bits is exact. -/
private theorem filter_add_exact (a b : Int32) (fits : (a.toInt + b.toInt).natAbs < 2 ^ 31) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A difference that fits in 32 bits is exact. -/
private theorem filter_sub_exact (a b : Int32) (fits : (a.toInt - b.toInt).natAbs < 2 ^ 31) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int32.toInt_sub]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A 32-bit unsigned number below 2^31 keeps its value as a signed one. -/
private theorem filter_small_toInt32 (u : UInt32) (small : u.toNat < 2 ^ 31) :
    u.toInt32.toInt = u.toNat := by
  show u.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · rfl
  · simp; omega

/-- A coefficient of at most 32767 times a value within ±65536: exact, and at most 32767 × 65536 in size
(under 2^31). -/
private theorem filter_scale (c : UInt32) (v : Int32) (bc : c.toNat ≤ 32767) (lo : -65536 ≤ v.toInt)
    (hi : v.toInt ≤ 65536) :
    (c.toInt32 * v).toInt = c.toNat * v.toInt ∧
      -(32767 * 65536) ≤ (c.toNat : Int) * v.toInt ∧ (c.toNat : Int) * v.toInt ≤ 32767 * 65536 := by
  have cv := filter_small_toInt32 c (by omega)
  have bound : ((c.toNat : Int) * v.toInt).natAbs ≤ 32767 * 65536 := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]; exact Nat.mul_le_mul bc (by omega)
  refine ⟨by rw [filter_mul_exact _ _ (by rw [cv]; omega), cv], by omega, by omega⟩

/-- What the hold does, for a bound that is not negative: the result is within the bound; a value already
within it is untouched; and the hold keeps the sign and never grows the value. -/
private theorem filter_hold_spec (y bound : Int32) (nonneg : 0 ≤ bound.toInt) :
    (-bound.toInt ≤ (Filter.hold y bound).toInt ∧ (Filter.hold y bound).toInt ≤ bound.toInt) ∧
      (-bound.toInt ≤ y.toInt → y.toInt ≤ bound.toInt → Filter.hold y bound = y) ∧
      (0 ≤ y.toInt → 0 ≤ (Filter.hold y bound).toInt ∧ (Filter.hold y bound).toInt ≤ y.toInt) ∧
      (y.toInt ≤ 0 → y.toInt ≤ (Filter.hold y bound).toInt ∧ (Filter.hold y bound).toInt ≤ 0) := by
  have hi := Int32.toInt_lt bound
  have neg : (-bound).toInt = -bound.toInt := by
    rw [Int32.toInt_neg]; exact Int.bmod_eq_of_le (by omega) (by omega)
  unfold Filter.hold
  split
  · rename_i h; have := Int32.lt_iff_toInt_lt.mp h
    exact ⟨by omega, fun a b => by omega, fun _ => by omega, fun _ => by omega⟩
  · split
    · rename_i h1 h2; have := Int32.lt_iff_toInt_lt.mp h2; rw [neg] at this
      rw [neg]
      exact ⟨by omega, fun a b => by omega, fun _ => by omega, fun _ => by omega⟩
    · rename_i h1 h2
      have a := Int32.le_iff_toInt_le.mp (Int32.not_lt.mp h1)
      have b := Int32.le_iff_toInt_le.mp (Int32.not_lt.mp h2); rw [neg] at b
      exact ⟨by omega, fun _ _ => rfl, fun _ => by omega, fun _ => by omega⟩

/-- With the cutoff fully open (100) and no resonance the filter is inactive: a step returns the sample and
the states unchanged, for any state, mode and sample.
Why it matters: these are the default settings on every voice, so every existing sound is bit for bit what
it was. -/
theorem filter_open_is_identity (mode : UInt32) (ic1 ic2 x : Int32) :
    Filter.active 100 0 = false ∧ Filter.step 100 0 mode ic1 ic2 x = ⟨x, ic1, ic2⟩ := by
  constructor
  · decide
  · simp [Filter.step, Filter.active]

/-- The states and nodes stay within ±65536 and nothing in a sample wraps: a state after a sample is within
±65536 for any inputs (the hold); and with both states within ±65536, the sample within ±65536 and the
coefficients in range (`g`, `a1`, `a2` at most 32767, `k` at most 16384) the band node before its hold is
exactly `a1 ic1 / 2^15 + a2 ((x - ic2) / 2) / 2^14`, the held band node `v1` is within ±65536, the low-pass
node `v2` is exactly `ic2 + g v1 / 2^15` and within ±131072, the high-pass output before its clip is exactly
`x - k v1 / 2^13 - v2`, the raw output of every mode is within ±327680 (5 · 2^16), and both state updates
`2 v - ic` are exact.
Why it matters: the filter's arithmetic saturates at twice full scale and never wraps, whatever the engine
feeds it; the clip to ±32767 at the output is the only other thing that touches a sample. -/
theorem filter_states_stay_bounded (ic1 ic2 x : Int32) (g a1 a2 k mode : UInt32)
    (s1 : ic1.toInt.natAbs ≤ 65536) (s2 : ic2.toInt.natAbs ≤ 65536) (sample : x.toInt.natAbs ≤ 65536)
    (hg : g.toNat ≤ 32767) (h1 : a1.toNat ≤ 32767) (h2 : a2.toNat ≤ 32767) (hk : k.toNat ≤ 16384) :
    (∀ ic v : Int32, (Filter.next ic v).toInt.natAbs ≤ 65536) ∧
    (Filter.band ic1 ic2 x a1 a2).toInt =
        a1.toNat * ic1.toInt / 32768 + a2.toNat * ((x.toInt - ic2.toInt) / 2) / 16384 ∧
    (Filter.v1 ic1 ic2 x a1 a2).toInt.natAbs ≤ 65536 ∧
    (Filter.v2 ic2 (Filter.v1 ic1 ic2 x a1 a2) g).toInt =
        ic2.toInt + g.toNat * (Filter.v1 ic1 ic2 x a1 a2).toInt / 32768 ∧
    (Filter.v2 ic2 (Filter.v1 ic1 ic2 x a1 a2) g).toInt.natAbs ≤ 131072 ∧
    (Filter.raw 2 x (Filter.v1 ic1 ic2 x a1 a2) (Filter.v2 ic2 (Filter.v1 ic1 ic2 x a1 a2) g) k).toInt =
        x.toInt - k.toNat * (Filter.v1 ic1 ic2 x a1 a2).toInt / 8192 -
          (Filter.v2 ic2 (Filter.v1 ic1 ic2 x a1 a2) g).toInt ∧
    (Filter.raw mode x (Filter.v1 ic1 ic2 x a1 a2) (Filter.v2 ic2 (Filter.v1 ic1 ic2 x a1 a2) g)
        k).toInt.natAbs ≤ 327680 ∧
    (2 * Filter.v1 ic1 ic2 x a1 a2 - ic1).toInt = 2 * (Filter.v1 ic1 ic2 x a1 a2).toInt - ic1.toInt ∧
    (2 * Filter.v2 ic2 (Filter.v1 ic1 ic2 x a1 a2) g - ic2).toInt =
        2 * (Filter.v2 ic2 (Filter.v1 ic1 ic2 x a1 a2) g).toInt - ic2.toInt := by
  have b16 : (65536 : Int32).toInt = 65536 := by decide
  have two : (2 : Int32).toInt = 2 := by decide
  have S1 : -65536 ≤ ic1.toInt ∧ ic1.toInt ≤ 65536 := by omega
  have S2 : -65536 ≤ ic2.toInt ∧ ic2.toInt ≤ 65536 := by omega
  have SX : -65536 ≤ x.toInt ∧ x.toInt ≤ 65536 := by omega
  clear s1 s2 sample
  refine ⟨fun ic v => ?_, ?_⟩
  · have := (filter_hold_spec (2 * v - ic) 65536 (by rw [b16]; decide)).1
    rw [b16] at this; unfold Filter.next; omega
  -- the band node
  have d : (x - ic2).toInt = x.toInt - ic2.toInt := filter_sub_exact _ _ (by omega)
  have dh : ((x - ic2) >>> 1).toInt = (x.toInt - ic2.toInt) / 2 := by rw [filter_shift1, d]
  obtain ⟨p1, b1⟩ := filter_scale a1 ic1 h1 S1.1 S1.2
  obtain ⟨p2, b2⟩ := filter_scale a2 _ h2 (by rw [dh]; omega) (by rw [dh]; omega)
  have t1 : ((a1.toInt32 * ic1) >>> 15).toInt = a1.toNat * ic1.toInt / 32768 := by rw [filter_shift15, p1]
  have t2 : ((a2.toInt32 * ((x - ic2) >>> 1)) >>> 14).toInt =
      a2.toNat * ((x.toInt - ic2.toInt) / 2) / 16384 := by
    rw [filter_shift14, p2, dh]
  rw [dh] at b2
  clear p1 p2 d dh
  have band : (Filter.band ic1 ic2 x a1 a2).toInt =
      a1.toNat * ic1.toInt / 32768 + a2.toNat * ((x.toInt - ic2.toInt) / 2) / 16384 := by
    unfold Filter.band
    generalize (a1.toNat : Int) * ic1.toInt = q1 at *
    generalize (a2.toNat : Int) * ((x.toInt - ic2.toInt) / 2) = q2 at *
    rw [filter_add_exact _ _ (by rw [t1, t2]; omega), t1, t2]
  have bv1 : -65536 ≤ (Filter.v1 ic1 ic2 x a1 a2).toInt ∧ (Filter.v1 ic1 ic2 x a1 a2).toInt ≤ 65536 := by
    have := (filter_hold_spec (Filter.band ic1 ic2 x a1 a2) 65536 (by rw [b16]; decide)).1
    rw [b16] at this; exact this
  clear t1 t2 b1 b2
  generalize Filter.v1 ic1 ic2 x a1 a2 = v1 at *
  -- the low-pass node
  obtain ⟨p3, b3⟩ := filter_scale g v1 hg bv1.1 bv1.2
  have t3 : ((g.toInt32 * v1) >>> 15).toInt = g.toNat * v1.toInt / 32768 := by rw [filter_shift15, p3]
  have low : (Filter.v2 ic2 v1 g).toInt = ic2.toInt + g.toNat * v1.toInt / 32768 := by
    show (ic2 + ((g.toInt32 * v1) >>> 15)).toInt = _
    generalize (g.toNat : Int) * v1.toInt = q3 at *
    rw [filter_add_exact _ _ (by rw [t3]; omega), t3]
  have bv2 : -131072 ≤ (Filter.v2 ic2 v1 g).toInt ∧ (Filter.v2 ic2 v1 g).toInt ≤ 131072 := by
    rw [low]; generalize (g.toNat : Int) * v1.toInt = q3 at *; omega
  clear p3 t3
  generalize Filter.v2 ic2 v1 g = v2 at *
  -- the high-pass output
  obtain ⟨p4, b4⟩ := filter_scale k v1 (by omega) bv1.1 bv1.2
  have t4 : ((k.toInt32 * v1) >>> 13).toInt = k.toNat * v1.toInt / 8192 := by rw [filter_shift13, p4]
  have kb : ((k.toNat : Int) * v1.toInt).natAbs ≤ 16384 * 65536 := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]; exact Nat.mul_le_mul hk (by omega)
  have kb' : -(16384 * 65536) ≤ (k.toNat : Int) * v1.toInt ∧ (k.toNat : Int) * v1.toInt ≤ 16384 * 65536 := by
    omega
  clear kb b4 p4
  have high : (Filter.raw 2 x v1 v2 k).toInt = x.toInt - k.toNat * v1.toInt / 8192 - v2.toInt := by
    show (x - ((k.toInt32 * v1) >>> 13) - v2).toInt = _
    generalize (k.toNat : Int) * v1.toInt = q4 at *
    have inner : (x - ((k.toInt32 * v1) >>> 13)).toInt = x.toInt - q4 / 8192 := by
      rw [filter_sub_exact _ _ (by rw [t4]; omega), t4]
    rw [filter_sub_exact _ _ (by rw [inner]; omega), inner]
  refine ⟨band, by omega, low, by omega, high, ?_, ?_, ?_⟩
  · generalize (k.toNat : Int) * v1.toInt = q4 at *
    rw [Filter.raw.eq_3 2 x v1 v2 k (by decide) (by decide)] at high
    by_cases m0 : mode = 0
    · subst m0; rw [Filter.raw.eq_1]; omega
    · by_cases m1 : mode = 1
      · subst m1; rw [Filter.raw.eq_2]; omega
      · rw [Filter.raw.eq_3 mode x v1 v2 k m0 m1, high]; omega
  · have m : (2 * v1).toInt = 2 * v1.toInt := by rw [filter_mul_exact _ _ (by rw [two]; omega), two]
    rw [filter_sub_exact _ _ (by rw [m]; omega), m]
  · have m : (2 * v2).toInt = 2 * v2.toInt := by rw [filter_mul_exact _ _ (by rw [two]; omega), two]
    rw [filter_sub_exact _ _ (by rw [m]; omega), m]

/-- Checked in the kernel: the cutoff table rises at every one of its 100 steps. -/
private theorem filter_table_rises :
    ∀ c : Fin 100, Filter.g c.val.toUInt32 < Filter.g (c.val.toUInt32 + 1) := by
  decide +kernel

/-- The coefficients are in the ranges `filter_states_stay_bounded` needs and the cutoff sweep is monotone:
every entry of the cutoff table is at most 32767 and the table rises from each setting to the next below
100; the damping is between 884 (0.108 in Q13) and 16384 (2.0) for any resonance setting; `a1` is at most
32767 for any `g` and `k`, and `a2` is at most `g` for any `g` at most 32767.
Why it matters: turning the cutoff up always opens the filter, and no cutoff or resonance setting hands
the sample path a coefficient that could overflow a product. -/
theorem filter_coefficients_in_range (c r g k : UInt32) (hg : g.toNat ≤ 32767) :
    (Filter.g c).toNat ≤ 32767 ∧ (c < 100 → Filter.g c < Filter.g (c + 1)) ∧
      884 ≤ (Filter.k r).toNat ∧ (Filter.k r).toNat ≤ 16384 ∧
      (Filter.a1 g k).toNat ≤ 32767 ∧ (Filter.a2 g k).toNat ≤ g.toNat := by
  have l155 : (155 : UInt32).toNat = 155 := by decide
  have l16384 : (16384 : UInt32).toNat = 16384 := by decide
  have damping : 884 ≤ (Filter.k r).toNat ∧ (Filter.k r).toNat ≤ 16384 := by
    unfold Filter.k
    have m : (min r 100).toNat ≤ 100 := by
      rw [UInt32.min_def]; split
      · rename_i h; exact UInt32.le_iff_toNat_le.mp h
      · decide
    have prod : (155 * min r 100).toNat = 155 * (min r 100).toNat := by
      rw [UInt32.toNat_mul, l155]; exact Nat.mod_eq_of_lt (by omega)
    have le : 155 * min r 100 ≤ 16384 := by rw [UInt32.le_iff_toNat_le, prod, l16384]; omega
    rw [UInt32.toNat_sub_of_le _ _ le, prod, l16384]
    omega
  have a1 : (Filter.a1 g k).toNat ≤ 32767 := by
    unfold Filter.a1; rw [UInt32.min_def]; split
    · rename_i h; exact UInt32.le_iff_toNat_le.mp h
    · decide
  refine ⟨?_, ?_, damping.1, damping.2, a1, ?_⟩
  · unfold Filter.g; split <;> decide
  · intro h
    have h' := UInt32.lt_iff_toNat_lt.mp h
    have := filter_table_rises ⟨c.toNat, h'⟩
    simpa [UInt32.ofNat_toNat] using this
  · unfold Filter.a2
    have e : ((g * Filter.a1 g k) >>> 15).toNat = g.toNat * (Filter.a1 g k).toNat / 32768 := by
      rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt32.toNat_mul, Nat.mod_eq_of_lt]
      · rfl
      · calc g.toNat * (Filter.a1 g k).toNat ≤ 32767 * 32767 := Nat.mul_le_mul hg a1
          _ < 2 ^ 32 := by decide
    rw [e]
    have := Nat.mul_le_mul_left g.toNat a1
    generalize g.toNat * (Filter.a1 g k).toNat = p at *
    omega

/-- A settled constant is a fixed point of the active filter: with the band state at rest (`ic1 = 0`) and
the low-pass state at the sample (`ic2 = x`), a step gives low-pass output `x`, band and high outputs 0,
and the same states again, for any cutoff and resonance and any sample within ±32767.
Why it matters: a steady level passes through the low-pass unchanged at any cutoff, with no drift from
rounding, and the band and high outputs reject it. -/
theorem filter_settled_dc_holds (cutoff resonance mode : UInt32) (x : Int32)
    (sample : x.toInt.natAbs ≤ 32767) (on : Filter.active cutoff resonance = true) :
    Filter.step cutoff resonance 0 0 x x = ⟨x, 0, x⟩ ∧ Filter.step cutoff resonance 1 0 x x = ⟨0, 0, x⟩ ∧
      (2 ≤ mode → Filter.step cutoff resonance mode 0 x x = ⟨0, 0, x⟩) := by
  have b16 : (65536 : Int32).toInt = 65536 := by decide
  have b15 : (32767 : Int32).toInt = 32767 := by decide
  have two : (2 : Int32).toInt = 2 := by decide
  have z1 : (0 : Int32) >>> 1 = 0 := by decide
  have z13 : (0 : Int32) >>> 13 = 0 := by decide
  have z14 : (0 : Int32) >>> 14 = 0 := by decide
  have z15 : (0 : Int32) >>> 15 = 0 := by decide
  have v1 : ∀ a1 a2, Filter.v1 0 x x a1 a2 = 0 := by
    intro a1 a2
    have band : Filter.band 0 x x a1 a2 = 0 := by
      simp only [Filter.band, Int32.mul_zero, Int32.sub_self, z1, z14, z15, Int32.add_zero]
    rw [Filter.v1, band]; decide
  have v2 : ∀ g, Filter.v2 x 0 g = x := by
    intro g; simp only [Filter.v2, Int32.mul_zero, z15, Int32.add_zero]
  have hx : Filter.hold x 32767 = x :=
    (filter_hold_spec x 32767 (by rw [b15]; decide)).2.1 (by rw [b15]; omega) (by rw [b15]; omega)
  have n1 : Filter.next 0 0 = 0 := by decide
  have n2 : Filter.next x x = x := by
    unfold Filter.next
    have m : (2 * x).toInt = 2 * x.toInt := by rw [filter_mul_exact _ _ (by rw [two]; omega), two]
    have s : (2 * x - x).toInt = x.toInt := by rw [filter_sub_exact _ _ (by rw [m]; omega), m]; omega
    have e : 2 * x - x = x := Int32.toInt_inj.mp s
    rw [e]
    exact (filter_hold_spec x 65536 (by rw [b16]; decide)).2.1 (by rw [b16]; omega) (by rw [b16]; omega)
  have h0 : Filter.hold 0 32767 = 0 := by decide
  refine ⟨?_, ?_, fun hm => ?_⟩
  · simp only [Filter.step, on, ite_true, v1, v2, n1, n2, Filter.out, Filter.raw, hx]
  · simp only [Filter.step, on, ite_true, v1, v2, n1, n2, Filter.out, Filter.raw, h0]
  · have not0 : mode = 0 → False := fun h => by rw [h] at hm; exact absurd hm (by decide)
    have not1 : mode = 1 → False := fun h => by rw [h] at hm; exact absurd hm (by decide)
    simp only [Filter.step, on, ite_true, v1, v2, n1, n2, Filter.out, Filter.raw.eq_3 mode _ _ _ _ not0 not1,
      Int32.mul_zero, z13, Int32.sub_zero, Int32.sub_self, h0]

/-- A low-pass step with the band node at rest (`ic1 = 0`) lands between the low-pass state and the sample,
within one count of rounding below: `min x ic2 - 1 ≤ v2 ≤ max x ic2`, for any `g` and `a2` at most 32767,
any `a1`, and states and sample within ±65536.
Why it matters: the low-pass integrator only moves toward the input; a resonant peak comes from the band
state, which is held. -/
theorem filter_lowpass_steps_toward_input (ic2 x : Int32) (g a1 a2 : UInt32)
    (s2 : ic2.toInt.natAbs ≤ 65536) (sample : x.toInt.natAbs ≤ 65536) (hg : g.toNat ≤ 32767)
    (h2 : a2.toNat ≤ 32767) :
    min x.toInt ic2.toInt - 1 ≤ (Filter.v2 ic2 (Filter.v1 0 ic2 x a1 a2) g).toInt ∧
      (Filter.v2 ic2 (Filter.v1 0 ic2 x a1 a2) g).toInt ≤ max x.toInt ic2.toInt := by
  have b16 : (65536 : Int32).toInt = 65536 := by decide
  have S2 : -65536 ≤ ic2.toInt ∧ ic2.toInt ≤ 65536 := by omega
  have SX : -65536 ≤ x.toInt ∧ x.toInt ≤ 65536 := by omega
  clear s2 sample
  have d : (x - ic2).toInt = x.toInt - ic2.toInt := filter_sub_exact _ _ (by omega)
  have dh : ((x - ic2) >>> 1).toInt = (x.toInt - ic2.toInt) / 2 := by rw [filter_shift1, d]
  obtain ⟨p2, b2⟩ := filter_scale a2 _ h2 (by rw [dh]; omega) (by rw [dh]; omega)
  have cz : (a1.toInt32 * 0) >>> 15 = 0 := by rw [Int32.mul_zero]; decide
  have band : (Filter.band 0 ic2 x a1 a2).toInt = a2.toNat * ((x.toInt - ic2.toInt) / 2) / 16384 := by
    unfold Filter.band; rw [cz, Int32.zero_add, filter_shift14, p2, dh]
  have hold := filter_hold_spec (Filter.band 0 ic2 x a1 a2) 65536 (by rw [b16]; decide)
  rw [b16] at hold
  have bv1 : -65536 ≤ (Filter.v1 0 ic2 x a1 a2).toInt ∧ (Filter.v1 0 ic2 x a1 a2).toInt ≤ 65536 := hold.1
  obtain ⟨p3, b3⟩ := filter_scale g _ hg bv1.1 bv1.2
  have low : (Filter.v2 ic2 (Filter.v1 0 ic2 x a1 a2) g).toInt =
      ic2.toInt + g.toNat * (Filter.v1 0 ic2 x a1 a2).toInt / 32768 := by
    show (ic2 + ((g.toInt32 * Filter.v1 0 ic2 x a1 a2) >>> 15)).toInt = _
    have t3 := filter_shift15 (g.toInt32 * Filter.v1 0 ic2 x a1 a2)
    rw [p3] at t3
    generalize (g.toNat : Int) * (Filter.v1 0 ic2 x a1 a2).toInt = q at *
    rw [filter_add_exact _ _ (by rw [t3]; omega), t3]
  have between := hold.2.2
  clear hold p2 p3 d dh cz
  rw [low]
  unfold Filter.v1 at bv1 between b3 ⊢
  -- the products, with their sign-aware bounds
  have ha2 : (0 : Int) ≤ a2.toNat ∧ (a2.toNat : Int) ≤ 32767 := by omega
  have hgI : (0 : Int) ≤ g.toNat ∧ (g.toNat : Int) ≤ 32767 := by omega
  generalize hh : (x.toInt - ic2.toInt) / 2 = h at *
  generalize (Filter.hold (Filter.band 0 ic2 x a1 a2) 65536).toInt = w at *
  generalize (Filter.band 0 ic2 x a1 a2).toInt = v at *
  have pb : ((a2.toNat : Int) * h ≤ 32767 * h ∧ 0 ≤ (a2.toNat : Int) * h) ∨
      (32767 * h ≤ (a2.toNat : Int) * h ∧ (a2.toNat : Int) * h ≤ 0) := by
    rcases Int.le_total 0 h with hp | hn
    · exact Or.inl ⟨Int.mul_le_mul_of_nonneg_right ha2.2 hp, Int.mul_nonneg ha2.1 hp⟩
    · exact Or.inr ⟨Int.mul_le_mul_of_nonpos_right ha2.2 hn, Int.mul_nonpos_of_nonneg_of_nonpos ha2.1 hn⟩
  have qb : ((g.toNat : Int) * w ≤ 32767 * w ∧ 0 ≤ (g.toNat : Int) * w) ∨
      (32767 * w ≤ (g.toNat : Int) * w ∧ (g.toNat : Int) * w ≤ 0) := by
    rcases Int.le_total 0 w with hp | hn
    · exact Or.inl ⟨Int.mul_le_mul_of_nonneg_right hgI.2 hp, Int.mul_nonneg hgI.1 hp⟩
    · exact Or.inr ⟨Int.mul_le_mul_of_nonpos_right hgI.2 hn, Int.mul_nonpos_of_nonneg_of_nonpos hgI.1 hn⟩
  generalize (a2.toNat : Int) * h = p at *
  generalize (g.toNat : Int) * w = q at *
  -- the two floors, exactly: `p / 2^14` is on the far side of `2 h` from zero, `q / 2^15` on the far side of `w`
  -- (the rational relaxation omega works with cannot see these integer facts)
  have v_lo : h ≤ 0 → 2 * h ≤ p / 16384 := fun _ => Int.le_ediv_of_mul_le (by decide) (by omega)
  have v_hi : 0 ≤ h → p / 16384 ≤ 2 * h := fun _ => Int.ediv_le_of_le_mul (by decide) (by omega)
  have q_lo : w ≤ 0 → w ≤ q / 32768 := fun _ => Int.le_ediv_of_mul_le (by decide) (by omega)
  have q_hi : 0 ≤ w → q / 32768 ≤ w := fun _ => Int.ediv_le_of_le_mul (by decide) (by omega)
  omega
