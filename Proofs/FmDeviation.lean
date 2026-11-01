import Spec.Fm

/-! The FM voice's peak frequency deviation (`Firmware/Fm.lean`, `Spec/Fm.lean`): the sine is Lipschitz in
the phase (it moves by at most two per position, a position being 2^15 phase units), so an unmodulated
modulator's output moves by a bounded amount a sample (its increment in positions, times two, plus one for
the envelope's rounding), and the push it gives a carrier moves by at most its depth times that: the
carrier's instantaneous frequency stays within depth times the modulator's slew of its own increment. That
is the half of Carson's rule that is a theorem; the other half (that the spectrum reaches that far) is not. -/

/-- A 32-bit unsigned number below 2^31 keeps its value as a signed one. -/
private theorem fm_small_toInt32 (u : UInt32) (small : u.toNat < 2 ^ 31) : u.toInt32.toInt = u.toNat := by
  show u.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · rfl
  · simp; omega

/-- The quarter polynomial never passes 32767: it is held there. -/
private theorem fm_quarter_le (x : UInt32) : (Fm.quarter x).toNat ≤ 32767 := by
  unfold Fm.quarter
  rw [UInt32.min_def]
  split
  · rename_i h; exact UInt32.le_iff_toNat_le.mp h
  · decide

/-- The quarter polynomial on numbers: what `Fm.quarter` computes, since nothing in it wraps. -/
private def quarterN (x : Nat) : Nat :=
  let x2 := x * x / 32768
  let inner := 21167 - x2 * 2611 / 32768
  let outer := 51472 - x2 * inner / 32768
  min (x * outer / 32768) 32767

/-- A shift right by 15 is division by 32768. -/
private theorem fm_shr15 (u : UInt32) : (u >>> 15).toNat = u.toNat / 32768 := by
  rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl

/-- A product that fits in 32 bits is exact. -/
private theorem fm_mul_nat (a b : UInt32) (fits : a.toNat * b.toNat < 2 ^ 32) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [UInt32.toNat_mul, Nat.mod_eq_of_lt fits]

/-- In the quarter (positions up to 32767) `Fm.quarter` is the polynomial on numbers: nothing wraps. -/
private theorem fm_quarter_nat (x : UInt32) (inside : x.toNat ≤ 32767) :
    (Fm.quarter x).toNat = quarterN x.toNat := by
  simp only [Fm.quarter, quarterN]
  generalize hx2 : (x * x) >>> 15 = x2
  have x2v : x2.toNat = x.toNat * x.toNat / 32768 := by
    rw [← hx2, fm_shr15, fm_mul_nat]
    calc x.toNat * x.toNat ≤ 32767 * 32767 := Nat.mul_le_mul inside inside
      _ < 2 ^ 32 := by decide
  have x2Le : x2.toNat ≤ 32767 := by
    have : x.toNat * x.toNat ≤ 32767 * 32767 := Nat.mul_le_mul inside inside
    omega
  generalize hia : (x2 * 2611) >>> 15 = ia
  have iav : ia.toNat = x2.toNat * 2611 / 32768 := by
    rw [← hia, fm_shr15, fm_mul_nat]
    · rfl
    · calc x2.toNat * (2611 : UInt32).toNat ≤ 32767 * 2611 := Nat.mul_le_mul x2Le (by decide)
        _ < 2 ^ 32 := by decide
  have iaLe : ia.toNat ≤ 21167 := by
    have : x2.toNat * 2611 ≤ 32767 * 2611 := Nat.mul_le_mul x2Le (by decide)
    omega
  generalize hin : 21167 - ia = inner
  have innerv : inner.toNat = 21167 - ia.toNat := by
    rw [← hin, UInt32.toNat_sub_of_le]
    · rfl
    · rw [UInt32.le_iff_toNat_le]; exact iaLe
  have innerLe : inner.toNat ≤ 21167 := by omega
  generalize hoa : (x2 * inner) >>> 15 = oa
  have oav : oa.toNat = x2.toNat * inner.toNat / 32768 := by
    rw [← hoa, fm_shr15, fm_mul_nat]
    calc x2.toNat * inner.toNat ≤ 32767 * 21167 := Nat.mul_le_mul x2Le innerLe
      _ < 2 ^ 32 := by decide
  have oaLe : oa.toNat ≤ 51472 := by
    have : x2.toNat * inner.toNat ≤ 32767 * 21167 := Nat.mul_le_mul x2Le innerLe
    omega
  generalize hout : 51472 - oa = outer
  have outerv : outer.toNat = 51472 - oa.toNat := by
    rw [← hout, UInt32.toNat_sub_of_le]
    · rfl
    · rw [UInt32.le_iff_toNat_le]; exact oaLe
  have outerLe : outer.toNat ≤ 51472 := by omega
  generalize htop : (x * outer) >>> 15 = top
  have topv : top.toNat = x.toNat * outer.toNat / 32768 := by
    rw [← htop, fm_shr15, fm_mul_nat]
    calc x.toNat * outer.toNat ≤ 32767 * 51472 := Nat.mul_le_mul inside outerLe
      _ < 2 ^ 32 := by decide
  rw [← x2v, ← iav, ← innerv, ← oav, ← outerv, ← topv, UInt32.min_def, Nat.min_def]
  split
  · rename_i h
    have h' : top.toNat ≤ 32767 := UInt32.le_iff_toNat_le.mp h
    rw [ite_eq_left h']
  · rename_i h
    have h' : ¬ top.toNat ≤ 32767 := fun le => h (UInt32.le_iff_toNat_le.mpr le)
    rw [ite_eq_right h']; rfl

/-- The sine at a position on numbers: `sinePos` on the position as a number. -/
private def sineN (pos : Nat) : Int :=
  let y : Int := quarterN (if pos / 32768 % 2 = 1 then 32767 - pos % 32768 else pos % 32768)
  if pos / 32768 ≥ 2 then -y else y

/-- The sine at a position (the top 17 bits of a phase): `Fm.sineAt` read through `Fm.position`. -/
private def sinePos (pos : UInt32) : Int32 :=
  let x := pos &&& 0x7FFF
  let y := (Fm.quarter (if (pos >>> 15) &&& 1 = 1 then 32767 - x else x)).toInt32
  if pos >>> 15 ≥ 2 then -y else y

/-- A shift by 30 is a shift by 15 twice. -/
private theorem fm_shift30 (p : UInt32) : p >>> 30 = (p >>> 15) >>> 15 := by
  rw [← UInt32.toNat_inj, UInt32.toNat_shiftRight, UInt32.toNat_shiftRight, UInt32.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
  rfl

/-- The sine at a phase is the sine at its position: `Fm.sineAt` depends on the phase only through
`Fm.position`. -/
private theorem fm_sine_eq_pos (p : UInt32) : Fm.sineAt p = sinePos (Fm.position p) := by
  show Fm.sineAt p = sinePos (p >>> 15)
  simp only [Fm.sineAt, Fm.folded, sinePos, fm_shift30]

/-- The sine at a position is the sine on numbers: the quadrant is the position over 32768, the place in it
the remainder, and nothing wraps. -/
private theorem fm_sine_pos_nat (pos : UInt32) :
    (sinePos pos).toInt = sineN pos.toNat := by
  have place : (pos &&& 0x7FFF).toNat = pos.toNat % 32768 := by
    rw [UInt32.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod pos.toNat 15
  have odd : ((pos >>> 15) &&& 1 = 1) ↔ (pos.toNat / 32768 % 2 = 1) := by
    rw [← UInt32.toNat_inj, UInt32.toNat_and, fm_shr15]
    show pos.toNat / 32768 &&& 1 = 1 ↔ _
    rw [Nat.and_one_is_mod]
  have half : ((pos >>> 15) ≥ 2) ↔ (pos.toNat / 32768 ≥ 2) := by
    rw [ge_iff_le, ge_iff_le, UInt32.le_iff_toNat_le, fm_shr15]; rfl
  have mirror : (32767 - (pos &&& 0x7FFF)).toNat = 32767 - pos.toNat % 32768 := by
    rw [UInt32.toNat_sub_of_le, place]
    · rfl
    · rw [UInt32.le_iff_toNat_le, place]; show _ ≤ 32767; omega
  simp only [sinePos, sineN]
  generalize hf : (if (pos >>> 15) &&& 1 = 1 then 32767 - (pos &&& 0x7FFF) else pos &&& 0x7FFF) = f
  have fval : f.toNat =
      if pos.toNat / 32768 % 2 = 1 then 32767 - pos.toNat % 32768 else pos.toNat % 32768 := by
    rw [← hf]
    by_cases h : pos.toNat / 32768 % 2 = 1
    · rw [ite_eq_left (odd.mpr h), ite_eq_left h, mirror]
    · rw [ite_eq_right (mt odd.mp h), ite_eq_right h, place]
  have fLe : f.toNat ≤ 32767 := by rw [fval]; split <;> omega
  have q := fm_quarter_nat f fLe
  have ql := fm_quarter_le f
  have small := fm_small_toInt32 (Fm.quarter f) (by omega)
  rw [fval] at q
  by_cases g : pos.toNat / 32768 ≥ 2
  · rw [ite_eq_left (half.mpr g), ite_eq_left g, Int32.toInt_neg, Int.bmod_eq_of_le (by omega) (by omega),
      small, q]
  · rw [ite_eq_right (mt half.mp g), ite_eq_right g, small, q]

/-- Checked for every position in a quarter (split for the kernel): the polynomial at the next position is
within two above or below. -/
private theorem fm_every_quarter_step :
    ∀ hi : Fin 128, ∀ lo : Fin 256, hi.val * 256 + lo.val < 32767 →
      quarterN (hi.val * 256 + lo.val) ≤ quarterN (hi.val * 256 + lo.val + 1) + 2 ∧
        quarterN (hi.val * 256 + lo.val + 1) ≤ quarterN (hi.val * 256 + lo.val) + 2 := by
  decide +kernel

/-- The quarter polynomial moves by at most two from a position to the next, however they are written. -/
private theorem fm_quarter_step (x y : Nat) (inside : x < 32767) (next : y = x + 1) :
    (quarterN y : Int) - quarterN x ≤ 2 ∧ (quarterN x : Int) - quarterN y ≤ 2 := by
  have split : x / 256 * 256 + x % 256 = x := by have := Nat.div_add_mod x 256; omega
  have := fm_every_quarter_step ⟨x / 256, by omega⟩ ⟨x % 256, Nat.mod_lt _ (by decide)⟩
    (by show x / 256 * 256 + x % 256 < 32767; omega)
  simp only at this
  rw [split] at this
  subst next
  omega

/-- The sine on numbers moves by at most two from a position to the next round the circle: within a quadrant
that is a step of the quarter polynomial (mirrored in the odd quadrants), and at the four quadrant boundaries
the two positions read the same quarter value (32767 at the peaks, 0 at the zero crossings). -/
private theorem fm_sine_step (k : Nat) (inside : k < 131072) :
    (sineN ((k + 1) % 131072) - sineN k).natAbs ≤ 2 := by
  have zero : quarterN 0 = 0 := by decide
  simp only [sineN]
  rcases (by omega : k % 32768 < 32767 ∨ k % 32768 = 32767) with mid | edge
  · have same : (k + 1) % 131072 / 32768 = k / 32768 := by omega
    have next : (k + 1) % 131072 % 32768 = k % 32768 + 1 := by omega
    rw [same, next]
    by_cases g : k / 32768 ≥ 2 <;> by_cases h : k / 32768 % 2 = 1 <;> simp only [g, h, ite_true, ite_false]
    all_goals first
      | (have := fm_quarter_step (k % 32768) (k % 32768 + 1) (by omega) rfl; omega)
      | (have := fm_quarter_step (32767 - (k % 32768 + 1)) (32767 - k % 32768) (by omega) (by omega); omega)
  · have q1 : (k + 1) % 131072 / 32768 = (k / 32768 + 1) % 4 := by omega
    have r1 : (k + 1) % 131072 % 32768 = 0 := by omega
    rw [q1, r1, edge]
    rcases (by omega : k / 32768 = 0 ∨ k / 32768 = 1 ∨ k / 32768 = 2 ∨ k / 32768 = 3) with q | q | q | q <;>
      rw [q] <;> simp [zero]

/-- The sine at position `k` round the circle of 131072 positions. -/
private def sineRound (k : Nat) : Int := sineN (k % 131072)

/-- One position on, the sine moves by at most two. -/
private theorem fm_round_step (k : Nat) : (sineRound (k + 1) - sineRound k).natAbs ≤ 2 := by
  have := fm_sine_step (k % 131072) (Nat.mod_lt _ (by decide))
  rw [show (k % 131072 + 1) % 131072 = (k + 1) % 131072 by omega] at this
  unfold sineRound
  exact this

/-- `m` positions on, the sine moves by at most `2 m`. -/
private theorem fm_round_walk (k m : Nat) : (sineRound (k + m) - sineRound k).natAbs ≤ 2 * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have := fm_round_step (k + m)
    rw [← Nat.add_assoc]
    omega

/-- The sine at a phase given as a number (modulo 2^32, as the phase is), through the position. -/
private theorem fm_sine_nat (t : Nat) : (Fm.sineAt t.toUInt32).toInt = sineRound (t / 2 ^ 15) := by
  rw [fm_sine_eq_pos, fm_sine_pos_nat]
  unfold sineRound Fm.position
  congr 1
  rw [fm_shr15, Nat.toUInt32_eq, UInt32.toNat_ofNat']
  omega

/-- From a phase to one `m` on (modulo 2^32), the sine moves by at most two per position crossed. -/
private theorem fm_sine_walk (t m : Nat) :
    ((Fm.sineAt (t + m).toUInt32).toInt - (Fm.sineAt t.toUInt32).toInt).natAbs ≤ 2 * (m / 2 ^ 15 + 1) := by
  rw [fm_sine_nat, fm_sine_nat]
  have steps : (t + m) / 2 ^ 15 = t / 2 ^ 15 + ((t + m) / 2 ^ 15 - t / 2 ^ 15) := by omega
  have few : (t + m) / 2 ^ 15 - t / 2 ^ 15 ≤ m / 2 ^ 15 + 1 := by omega
  rw [steps]
  have := fm_round_walk (t / 2 ^ 15) ((t + m) / 2 ^ 15 - t / 2 ^ 15)
  omega

/-- The same for a 32-bit phase and a 32-bit step, the sum wrapping as the engine's does. -/
private theorem fm_sine_add (a m : UInt32) :
    ((Fm.sineAt (a + m)).toInt - (Fm.sineAt a).toInt).natAbs ≤ 2 * (m.toNat / 2 ^ 15 + 1) := by
  have := fm_sine_walk a.toNat m.toNat
  have sum : (a.toNat + m.toNat).toUInt32 = a + m := by
    rw [← UInt32.toNat_inj, UInt32.toNat_add, Nat.toUInt32_eq, UInt32.toNat_ofNat']
  have back : a.toNat.toUInt32 = a := UInt32.ofNat_toNat
  rw [sum, back] at this
  exact this

/-- The sine is Lipschitz in the phase: between two phases it moves by at most two per position (2^15 phase
units) crossed, counting one more for the partial positions at either end.
Why it matters: the sine an operator reads cannot jump: a phase that moves by a small increment reads a value
that moves by a bounded amount, which is what makes a modulator's output smooth and a carrier's frequency
deviation bounded (`fm_modulator_slew`, `fm_carrier_frequency_deviation`). -/
theorem fm_sine_lipschitz (a b : UInt32) (order : a.toNat ≤ b.toNat) :
    ((Fm.sineAt b).toInt - (Fm.sineAt a).toInt).natAbs ≤ 2 * ((b.toNat - a.toNat) / 2 ^ 15 + 1) := by
  have := fm_sine_walk a.toNat (b.toNat - a.toNat)
  rw [show a.toNat + (b.toNat - a.toNat) = b.toNat by omega, Nat.toUInt32_eq, Nat.toUInt32_eq,
    UInt32.ofNat_toNat, UInt32.ofNat_toNat] at this
  exact this

/-- An arithmetic shift right of a 32-bit number by 16 is division by 65536, rounding down. -/
private theorem fm_shift16 (x : Int32) : (x >>> 16).toInt = x.toInt / 65536 := by
  show (x >>> 16).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- A product that fits in 32 bits is exact. -/
private theorem fm_mul_exact (a b : Int32) (fits : (a.toInt * b.toInt).natAbs < 2 ^ 31) :
    (a * b).toInt = a.toInt * b.toInt := by
  rw [Int32.toInt_mul]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- The sine is a quarter value with a sign: between -32767 and 32767, for every phase. -/
private theorem fm_sine_bounded (phase : UInt32) : (Fm.sineAt phase).toInt.natAbs ≤ 32767 := by
  simp only [Fm.sineAt]
  have q := fm_quarter_le (Fm.folded phase)
  have v := fm_small_toInt32 (Fm.quarter (Fm.folded phase)) (by omega)
  generalize Fm.quarter (Fm.folded phase) = y at *
  split
  · rw [Int32.toInt_neg, Int.bmod_eq_of_le (by omega) (by omega)]; omega
  · omega

/-- An unmodulated operator's output is its sine scaled by its envelope, rounding down; nothing wraps. -/
private theorem fm_operator_eq (phase env : UInt32) (unit : env.toNat ≤ 2 ^ 24) :
    (Fm.operator phase 0 env).toInt = (Fm.sineAt phase).toInt * ((env.toNat / 256 : Nat) : Int) / 65536 := by
  unfold Fm.operator
  rw [UInt32.add_zero]
  have s := fm_sine_bounded phase
  have e : (env >>> 8).toNat = env.toNat / 256 := by
    rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have ev := fm_small_toInt32 (env >>> 8) (by omega)
  have fits : ((Fm.sineAt phase).toInt * (env >>> 8).toInt32.toInt).natAbs < 2 ^ 31 := by
    rw [ev, Int.natAbs_mul]
    calc (Fm.sineAt phase).toInt.natAbs * ((env >>> 8).toNat : Int).natAbs ≤ 32767 * 65536 :=
        Nat.mul_le_mul s (by rw [Int.natAbs_natCast, e]; omega)
      _ < 2 ^ 31 := by decide
  rw [fm_shift16, fm_mul_exact _ _ fits, ev, e]

/-- Two values within `d` of each other, scaled by an envelope up to one and rounded down, stay within
`d + 1`. -/
private theorem fm_scale_close (s s' : Int) (l d : Nat) (unit : l ≤ 65536) (close : (s' - s).natAbs ≤ d) :
    (s' * l / 65536 - s * l / 65536).natAbs ≤ d + 1 := by
  have prod : ((s' - s) * l).natAbs ≤ d * 65536 := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]; exact Nat.mul_le_mul close unit
  rw [Int.sub_mul] at prod
  generalize s' * (l : Int) = u at *
  generalize s * (l : Int) = v at *
  omega

/-- An unmodulated operator at increment `incM` and envelope `env` (at most one) changes by at most
`2 (incM / 2^15 + 1) + 1` a sample: two per position its phase crosses, one for the envelope scaling's
rounding. The phase wraps round the cycle as the engine's does; the sine is continuous across the wrap (both
ends are zero), so the wrap costs nothing.
Why it matters: a modulator's output moves slowly when its frequency is low and faster when it is high, in
proportion to its increment: the slew is the modulator's frequency in disguise, which is what makes FM's
frequency deviation proportional to the modulating frequency. -/
theorem fm_modulator_slew (p incM env : UInt32) (unit : env.toNat ≤ 2 ^ 24) (n : Nat) :
    ((Fm.operator (Fm.phaseAfter p incM (n + 1)) 0 env).toInt -
        (Fm.operator (Fm.phaseAfter p incM n) 0 env).toInt).natAbs ≤ 2 * (incM.toNat / 2 ^ 15 + 1) + 1 := by
  rw [fm_operator_eq _ _ unit, fm_operator_eq _ _ unit]
  exact fm_scale_close _ _ _ _ (by omega) (fm_sine_add (Fm.phaseAfter p incM n) incM)

/-- A carrier at increment `incC` pushed by a modulator (`Fm.push 0 out depth`, `out` the modulator's output
at each sample): the push changes from one sample to the next by `depth` times the change in the modulator's
output (as 32-bit numbers, modulo 2^32), so the carrier's pushed phase advances by `incC` plus that term;
the change in the modulator's output is at most `2 (incM / 2^15 + 1) + 1` (`fm_modulator_slew`), so the
change in the push, as an integer, is at most `depth` times that.
Why it matters: the carrier's instantaneous frequency is its own increment plus `depth` times the modulator's
slew, so the peak frequency deviation is at most `depth (2 (incM / 2^15 + 1) + 1)` phase units a sample:
proportional to the modulation index times the modulator's frequency, the half of Carson's rule that says how
wide a shape's spectrum can get for a given depth and ratio. -/
theorem fm_carrier_frequency_deviation (c incC p incM env depth : UInt32) (unit : env.toNat ≤ 2 ^ 24)
    (n : Nat) :
    let out := fun k => Fm.operator (Fm.phaseAfter p incM k) 0 env
    Fm.push 0 (out (n + 1)) depth - Fm.push 0 (out n) depth = (out (n + 1) - out n).toUInt32 * depth ∧
      (Fm.phaseAfter c incC (n + 1) + Fm.push 0 (out (n + 1)) depth) -
          (Fm.phaseAfter c incC n + Fm.push 0 (out n) depth) =
        incC + (out (n + 1) - out n).toUInt32 * depth ∧
      ((out (n + 1)).toInt - (out n).toInt).natAbs ≤ 2 * (incM.toNat / 2 ^ 15 + 1) + 1 ∧
      (depth.toNat * ((out (n + 1)).toInt - (out n).toInt)).natAbs ≤
        depth.toNat * (2 * (incM.toNat / 2 ^ 15 + 1) + 1) := by
  intro out
  have diff : Fm.push 0 (out (n + 1)) depth - Fm.push 0 (out n) depth =
      (out (n + 1) - out n).toUInt32 * depth := by
    show 0 + (out (n + 1)).toUInt32 * depth - (0 + (out n).toUInt32 * depth) = _
    rw [UInt32.zero_add, UInt32.zero_add, Int32.toUInt32_sub, UInt32.sub_mul]
  have slew := fm_modulator_slew p incM env unit n
  refine ⟨diff, ?_, slew, by rw [Int.natAbs_mul, Int.natAbs_natCast]; exact Nat.mul_le_mul_left _ slew⟩
  rw [← diff]
  show Fm.phaseAfter c incC n + incC + Fm.push 0 (out (n + 1)) depth -
      (Fm.phaseAfter c incC n + Fm.push 0 (out n) depth) = _
  generalize Fm.phaseAfter c incC n = a
  generalize Fm.push 0 (out (n + 1)) depth = x
  generalize Fm.push 0 (out n) depth = y
  rw [UInt32.sub_eq_iff_eq_add]
  calc a + incC + x = incC + ((x - y + y) + a) := by rw [UInt32.sub_add_cancel]; ac_rfl
    _ = incC + (x - y) + (a + y) := by ac_rfl
