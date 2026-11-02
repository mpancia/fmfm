import Spec.Fm

/-! The FM voice's envelopes (`Fm.envelopeStep`, `Fm.envelopeAfter`): a block takes a share `rate / 2^20` of
what is left, exactly, up to rounding; so after `k` blocks the envelope is at most its start times
`(1 - rate / 2^20)^k` plus the roundings; rate 0 holds exactly; and the shapes' modulators and tines are
gone in the times the kernel computes from the actual rates. -/

/-- A block's envelope, exactly: what was there, less the share `envelope / 256 * rate / 4096` (rounded
down twice), for any envelope up to one (2^24) and rate below 65536; nothing wraps. -/
private theorem fm_step_eq (e r : UInt32) (unit : e.toNat ≤ 2 ^ 24) (small : r.toNat < 65536) :
    (Fm.envelopeStep e r).toNat = e.toNat - e.toNat / 256 * r.toNat / 4096 := by
  unfold Fm.envelopeStep
  have top : (e >>> 8).toNat = e.toNat / 256 := by
    rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have prod : ((e >>> 8) * r).toNat = e.toNat / 256 * r.toNat := by
    rw [UInt32.toNat_mul, top, Nat.mod_eq_of_lt]
    calc e.toNat / 256 * r.toNat ≤ 65536 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      _ < 2 ^ 32 := by decide
  have share : (((e >>> 8) * r) >>> 12).toNat = e.toNat / 256 * r.toNat / 4096 := by
    rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, prod]; rfl
  have le : e.toNat / 256 * r.toNat / 4096 ≤ e.toNat := by
    calc e.toNat / 256 * r.toNat / 4096 ≤ e.toNat / 256 * 65536 / 4096 :=
          Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))
      _ = e.toNat / 256 * 16 := by
          rw [show (65536 : Nat) = 16 * 4096 by rfl, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide)]
      _ ≤ e.toNat := by omega
  rw [UInt32.toNat_sub_of_le, share]
  rw [UInt32.le_iff_toNat_le, share]; exact le

/-- A block scales the envelope by `(2^20 - rate) / 2^20` and the two roundings add at most 17 counts
(a count being 1/2^24): `256 * 4095` from the share and `255 * rate` from the top bits, under `17 * 2^20`. -/
private theorem fm_step_scales (e r : UInt32) (unit : e.toNat ≤ 2 ^ 24) (small : r.toNat < 65536) :
    (Fm.envelopeStep e r).toNat ≤ e.toNat ∧
      (Fm.envelopeStep e r).toNat * 2 ^ 20 ≤ e.toNat * (2 ^ 20 - r.toNat) + 17 * 2 ^ 20 := by
  rw [fm_step_eq e r unit small]
  refine ⟨Nat.sub_le _ _, ?_⟩
  have split : e.toNat ≤ 256 * (e.toNat / 256) + 255 := by omega
  have top : e.toNat * r.toNat ≤ 256 * (e.toNat / 256 * r.toNat) + 255 * r.toNat := by
    have := Nat.mul_le_mul_right r.toNat split
    rw [Nat.add_mul, Nat.mul_assoc] at this
    exact this
  rw [Nat.mul_sub, Nat.sub_mul]
  generalize e.toNat / 256 * r.toNat = d at *
  generalize e.toNat * r.toNat = p at *
  omega

/-- The envelope after `k` blocks at `rate` is at most its start times `((2^20 - rate) / 2^20)^k` plus 17
counts a block for rounding (both sides scaled by `2^20^k` to stay in whole numbers), for any start up to
one (2^24) and rate below 65536; and it never passes one.
Why it matters: an envelope decays geometrically with time constant `2^20 / rate` blocks; rounding cannot
pile up into a floor. -/
theorem fm_envelope_after_bounded (e r : UInt32) (unit : e.toNat ≤ 2 ^ 24) (small : r.toNat < 65536)
    (k : Nat) :
    (Fm.envelopeAfter e r k).toNat ≤ 2 ^ 24 ∧
      (Fm.envelopeAfter e r k).toNat * (2 ^ 20) ^ k ≤
        e.toNat * (2 ^ 20 - r.toNat) ^ k + 17 * k * (2 ^ 20) ^ k := by
  induction k with
  | zero => simp [Fm.envelopeAfter, unit]
  | succ k ih =>
    obtain ⟨fits, ih⟩ := ih
    have ⟨falls, mono⟩ := fm_step_scales (Fm.envelopeAfter e r k) r fits small
    refine ⟨Nat.le_trans falls fits, ?_⟩
    show (Fm.envelopeStep (Fm.envelopeAfter e r k) r).toNat * (2 ^ 20) ^ (k + 1) ≤ _
    generalize (Fm.envelopeStep (Fm.envelopeAfter e r k) r).toNat = x at *
    generalize (Fm.envelopeAfter e r k).toNat = y at *
    generalize e.toNat = s at *
    have cle : 2 ^ 20 - r.toNat ≤ 2 ^ 20 := Nat.sub_le _ _
    generalize 2 ^ 20 - r.toNat = c at *
    generalize (2 ^ 20 : Nat) = m at *
    calc x * m ^ (k + 1) = x * m * m ^ k := by rw [Nat.pow_succ]; ac_rfl
      _ ≤ (y * c + 17 * m) * m ^ k := Nat.mul_le_mul_right _ mono
      _ = y * m ^ k * c + 17 * m * m ^ k := by rw [Nat.add_mul]; ac_rfl
      _ ≤ (s * c ^ k + 17 * k * m ^ k) * c + 17 * m * m ^ k :=
          Nat.add_le_add_right (Nat.mul_le_mul_right c ih) _
      _ = s * c ^ (k + 1) + 17 * k * (m ^ k * c) + 17 * m * m ^ k := by
          rw [Nat.add_mul, Nat.pow_succ]; ac_rfl
      _ ≤ s * c ^ (k + 1) + 17 * k * (m ^ k * m) + 17 * m * m ^ k := by
          exact Nat.add_le_add_right (Nat.add_le_add_left
            (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ cle)) _) _
      _ = s * c ^ (k + 1) + 17 * (k + 1) * m ^ (k + 1) := by
          rw [Nat.pow_succ c, Nat.pow_succ m, Nat.mul_succ, Nat.add_mul]; ac_rfl

/-- At rate 0 the envelope holds exactly.
Why it matters: `0` in the rate table means hold with no drift from rounding (the piano's body, every organ
operator). -/
theorem fm_held_envelope_holds (e : UInt32) (k : Nat) : Fm.envelopeAfter e 0 k = e := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show Fm.envelopeStep (Fm.envelopeAfter e 0 k) 0 = e
    rw [ih]
    show e - ((0 : UInt32) >>> 12) = e
    rw [show ((0 : UInt32) >>> 12) = 0 from by decide, UInt32.sub_zero]

/-- The piano (shape 48): its decaying operators' tails, block by block in the kernel. -/
private theorem fm_tails_piano :
    -- op 2, rate 960: a tenth at 2515 blocks (0.91 s), a hundredth at 5033 (1.83 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 2) 2514).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 2) 2515).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 2) 5032).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 2) 5033).toNat < 2 ^ 24 / 100 ∧
    -- op 3, rate 480: a tenth at 5031 blocks (1.83 s), a hundredth at 10074 (3.65 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 3) 5030).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 3) 5031).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 3) 10073).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 3) 10074).toNat < 2 ^ 24 / 100 ∧
    -- op 4, rate 6400: a tenth at 377 blocks (0.14 s), a hundredth at 753 (0.27 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 4) 376).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 4) 377).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 4) 752).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 4) 753).toNat < 2 ^ 24 / 100 := by
  decide +kernel

/-- The bell (shape 49): its decaying operators' tails, block by block in the kernel. -/
private theorem fm_tails_bell :
    -- op 2, rate 400: a tenth at 6037 blocks (2.19 s), a hundredth at 12093 (4.39 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 2) 6036).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 2) 6037).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 2) 12092).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 2) 12093).toNat < 2 ^ 24 / 100 ∧
    -- op 3, rate 960: a tenth at 2515 blocks (0.91 s), a hundredth at 5033 (1.83 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 3) 2514).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 3) 2515).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 3) 5032).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 3) 5033).toNat < 2 ^ 24 / 100 ∧
    -- op 4, rate 640: a tenth at 3773 blocks (1.37 s), a hundredth at 7552 (2.74 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 4) 3772).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 4) 3773).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 4) 7551).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 4) 7552).toNat < 2 ^ 24 / 100 := by
  decide +kernel

/-- The bass (shape 50): its decaying operators' tails, block by block in the kernel. -/
private theorem fm_tails_bass :
    -- op 2, rate 1920: a tenth at 1257 blocks (0.46 s), a hundredth at 2514 (0.91 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 2) 1256).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 2) 1257).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 2) 2513).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 2) 2514).toNat < 2 ^ 24 / 100 ∧
    -- op 3, rate 3200: a tenth at 754 blocks (0.27 s), a hundredth at 1508 (0.55 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 3) 753).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 3) 754).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 3) 1507).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 3) 1508).toNat < 2 ^ 24 / 100 ∧
    -- op 4, rate 4800: a tenth at 502 blocks (0.18 s), a hundredth at 1005 (0.36 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 4) 501).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 4) 502).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 4) 1004).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 4) 1005).toNat < 2 ^ 24 / 100 := by
  decide +kernel

/-- The brass (shape 51): its decaying operators' tails, block by block in the kernel. -/
private theorem fm_tails_brass :
    -- op 2, rate 128: a tenth at 18880 blocks (6.85 s), a hundredth at 37926 (13.76 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 2) 18879).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 2) 18880).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 2) 37925).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 2) 37926).toNat < 2 ^ 24 / 100 ∧
    -- op 3, rate 192: a tenth at 12583 blocks (4.57 s), a hundredth at 25241 (9.16 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 3) 12582).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 3) 12583).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 3) 25240).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 3) 25241).toNat < 2 ^ 24 / 100 ∧
    -- op 4, rate 256: a tenth at 9435 blocks (3.42 s), a hundredth at 18911 (6.86 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 4) 9434).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 4) 9435).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 4) 18910).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 4) 18911).toNat < 2 ^ 24 / 100 := by
  decide +kernel

/-- The glass (shape 52): its decaying operators' tails, block by block in the kernel. -/
private theorem fm_tails_glass :
    -- op 4, rate 320: a tenth at 7548 blocks (2.74 s), a hundredth at 15122 (5.49 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 52 4) 7547).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 52 4) 7548).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 52 4) 15121).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 52 4) 15122).toNat < 2 ^ 24 / 100 := by
  decide +kernel

/-- The mallet (shape 53): its decaying operators' tails, block by block in the kernel. -/
private theorem fm_tails_mallet :
    -- op 2, rate 4000: a tenth at 603 blocks (0.22 s), a hundredth at 1206 (0.44 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 2) 602).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 2) 603).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 2) 1205).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 2) 1206).toNat < 2 ^ 24 / 100 ∧
    -- op 3, rate 8000: a tenth at 301 blocks (0.11 s), a hundredth at 602 (0.22 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 3) 300).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 3) 301).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 3) 601).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 3) 602).toNat < 2 ^ 24 / 100 ∧
    -- op 4, rate 11200: a tenth at 215 blocks (0.08 s), a hundredth at 429 (0.16 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 4) 214).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 4) 215).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 4) 428).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 4) 429).toNat < 2 ^ 24 / 100 := by
  decide +kernel

/-- The clang (shape 55): its decaying operators' tails, block by block in the kernel. -/
private theorem fm_tails_clang :
    -- op 2, rate 800: a tenth at 3018 blocks (1.09 s), a hundredth at 6040 (2.19 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 2) 3017).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 2) 3018).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 2) 6039).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 2) 6040).toNat < 2 ^ 24 / 100 ∧
    -- op 3, rate 1120: a tenth at 2155 blocks (0.78 s), a hundredth at 4313 (1.56 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 3) 2154).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 3) 2155).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 3) 4312).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 3) 4313).toNat < 2 ^ 24 / 100 ∧
    -- op 4, rate 1440: a tenth at 1676 blocks (0.61 s), a hundredth at 3354 (1.22 s)
    2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 4) 1675).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 4) 1676).toNat < 2 ^ 24 / 10 ∧
    2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 4) 3353).toNat ∧
      (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 4) 3354).toNat < 2 ^ 24 / 100 := by
  decide +kernel
/-- For every shape's decaying operators, from a full envelope (2^24) at the table's rate: the first block at
which the envelope is under a tenth, and under a hundredth, stepped block by block in the kernel, with the
block before still above (a block is 16 samples, 0.36 ms at 44.1 kHz). Under a hundredth: the piano's tine
(op 4) in 0.27 s, its modulator (op 2) in 1.8 s, its op 3 in 3.7 s; the bell's three partials in 1.8 to
4.4 s; the bass's modulators in 0.4 to 0.9 s; the brass's in 7 to 14 s; the glass's op 4 in 5.5 s; the
mallet's in 0.16 to 0.44 s; the clang's in 1.2 to 2.2 s. The organ and every shape's carriers hold
(`fm_held_envelope_holds`).
Why it matters: these are the decay times a player hears, computed from the arithmetic the chip runs. -/
theorem fm_shape_tails :
    -- piano
    (
      -- op 2, rate 960: a tenth at 2515 blocks (0.91 s), a hundredth at 5033 (1.83 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 2) 2514).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 2) 2515).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 2) 5032).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 2) 5033).toNat < 2 ^ 24 / 100 ∧
      -- op 3, rate 480: a tenth at 5031 blocks (1.83 s), a hundredth at 10074 (3.65 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 3) 5030).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 3) 5031).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 3) 10073).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 3) 10074).toNat < 2 ^ 24 / 100 ∧
      -- op 4, rate 6400: a tenth at 377 blocks (0.14 s), a hundredth at 753 (0.27 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 4) 376).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 4) 377).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 4) 752).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 48 4) 753).toNat < 2 ^ 24 / 100
    ) ∧
    -- bell
    (
      -- op 2, rate 400: a tenth at 6037 blocks (2.19 s), a hundredth at 12093 (4.39 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 2) 6036).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 2) 6037).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 2) 12092).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 2) 12093).toNat < 2 ^ 24 / 100 ∧
      -- op 3, rate 960: a tenth at 2515 blocks (0.91 s), a hundredth at 5033 (1.83 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 3) 2514).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 3) 2515).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 3) 5032).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 3) 5033).toNat < 2 ^ 24 / 100 ∧
      -- op 4, rate 640: a tenth at 3773 blocks (1.37 s), a hundredth at 7552 (2.74 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 4) 3772).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 4) 3773).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 4) 7551).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 49 4) 7552).toNat < 2 ^ 24 / 100
    ) ∧
    -- bass
    (
      -- op 2, rate 1920: a tenth at 1257 blocks (0.46 s), a hundredth at 2514 (0.91 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 2) 1256).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 2) 1257).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 2) 2513).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 2) 2514).toNat < 2 ^ 24 / 100 ∧
      -- op 3, rate 3200: a tenth at 754 blocks (0.27 s), a hundredth at 1508 (0.55 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 3) 753).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 3) 754).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 3) 1507).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 3) 1508).toNat < 2 ^ 24 / 100 ∧
      -- op 4, rate 4800: a tenth at 502 blocks (0.18 s), a hundredth at 1005 (0.36 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 4) 501).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 4) 502).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 4) 1004).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 50 4) 1005).toNat < 2 ^ 24 / 100
    ) ∧
    -- brass
    (
      -- op 2, rate 128: a tenth at 18880 blocks (6.85 s), a hundredth at 37926 (13.76 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 2) 18879).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 2) 18880).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 2) 37925).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 2) 37926).toNat < 2 ^ 24 / 100 ∧
      -- op 3, rate 192: a tenth at 12583 blocks (4.57 s), a hundredth at 25241 (9.16 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 3) 12582).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 3) 12583).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 3) 25240).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 3) 25241).toNat < 2 ^ 24 / 100 ∧
      -- op 4, rate 256: a tenth at 9435 blocks (3.42 s), a hundredth at 18911 (6.86 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 4) 9434).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 4) 9435).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 4) 18910).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 51 4) 18911).toNat < 2 ^ 24 / 100
    ) ∧
    -- glass
    (
      -- op 4, rate 320: a tenth at 7548 blocks (2.74 s), a hundredth at 15122 (5.49 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 52 4) 7547).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 52 4) 7548).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 52 4) 15121).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 52 4) 15122).toNat < 2 ^ 24 / 100
    ) ∧
    -- mallet
    (
      -- op 2, rate 4000: a tenth at 603 blocks (0.22 s), a hundredth at 1206 (0.44 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 2) 602).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 2) 603).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 2) 1205).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 2) 1206).toNat < 2 ^ 24 / 100 ∧
      -- op 3, rate 8000: a tenth at 301 blocks (0.11 s), a hundredth at 602 (0.22 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 3) 300).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 3) 301).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 3) 601).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 3) 602).toNat < 2 ^ 24 / 100 ∧
      -- op 4, rate 11200: a tenth at 215 blocks (0.08 s), a hundredth at 429 (0.16 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 4) 214).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 4) 215).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 4) 428).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 53 4) 429).toNat < 2 ^ 24 / 100
    ) ∧
    -- clang
    (
      -- op 2, rate 800: a tenth at 3018 blocks (1.09 s), a hundredth at 6040 (2.19 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 2) 3017).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 2) 3018).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 2) 6039).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 2) 6040).toNat < 2 ^ 24 / 100 ∧
      -- op 3, rate 1120: a tenth at 2155 blocks (0.78 s), a hundredth at 4313 (1.56 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 3) 2154).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 3) 2155).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 3) 4312).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 3) 4313).toNat < 2 ^ 24 / 100 ∧
      -- op 4, rate 1440: a tenth at 1676 blocks (0.61 s), a hundredth at 3354 (1.22 s)
      2 ^ 24 / 10 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 4) 1675).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 4) 1676).toNat < 2 ^ 24 / 10 ∧
      2 ^ 24 / 100 ≤ (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 4) 3353).toNat ∧
        (Fm.envelopeAfter (2 ^ 24) (Fm.rate 55 4) 3354).toNat < 2 ^ 24 / 100
    ) := by
  exact ⟨fm_tails_piano, fm_tails_bell, fm_tails_bass, fm_tails_brass, fm_tails_glass, fm_tails_mallet,
    fm_tails_clang⟩
