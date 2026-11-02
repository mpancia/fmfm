import Firmware.Punch
import Firmware.Mix

/-!
The PUNCH page's audio path: the mix (within 2^19 by `mix_machine_sample_bounded`) through the CRUSH hold
and the GATE's gain, with the limits the firmware keeps: a gate gain of at most one (32768, Q15).
-/

/-- A 32-bit product whose true value fits is exact. -/
private theorem punchmix_mul_exact (a b : Int32) (fits : (a.toInt * b.toInt).natAbs < 2 ^ 31) :
    (a * b).toInt = a.toInt * b.toInt := by
  rw [Int32.toInt_mul]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A 32-bit division (truncating toward zero) by a positive constant is exact: its size is within the
dividend's. -/
private theorem punchmix_div_exact (a b : Int32) (pos : 0 < b.toInt) :
    (a / b).toInt = a.toInt.tdiv b.toInt ∧ (a / b).toInt.natAbs ≤ a.toInt.natAbs := by
  have lo := Int32.le_toInt a
  have hi := Int32.toInt_lt a
  have size : (a.toInt.tdiv b.toInt).natAbs ≤ a.toInt.natAbs := by
    rw [Int.natAbs_tdiv]
    exact Nat.div_le_self _ _
  have exact : (a / b).toInt = a.toInt.tdiv b.toInt := by
    have signPos : 0 ≤ a.toInt → 0 ≤ a.toInt.tdiv b.toInt := fun pos => Int.tdiv_nonneg pos (by omega)
    have signNeg : a.toInt ≤ 0 → a.toInt.tdiv b.toInt ≤ 0 := fun neg => by
      have := Int.tdiv_nonneg (a := -a.toInt) (b := b.toInt) (by omega) (by omega)
      rw [Int.neg_tdiv] at this; omega
    rw [Int32.toInt_div]; exact Int.bmod_eq_of_le (by omega) (by omega)
  exact ⟨exact, by rw [exact]; exact size⟩

/-- A 32-bit unsigned number below 2^31 keeps its value as a signed one. -/
private theorem punchmix_small_toInt32 (u : UInt32) (small : u.toNat < 2 ^ 31) :
    u.toInt32.toInt = u.toNat := by
  show u.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · rfl
  · simp; omega

/-- The size of the gate's output: the sample's sixteenth (toward zero) times the gain, over 2048. -/
private theorem punchmix_gate_size (sample : Int32) (gain : UInt32) (inLimit : sample.toInt.natAbs ≤ 524287)
    (unit : gain.toNat ≤ 32768) :
    (Punch.gateSample sample gain).toInt.natAbs = sample.toInt.natAbs / 16 * gain.toNat / 2048 := by
  unfold Punch.gateSample
  have gv := punchmix_small_toInt32 gain (by omega)
  have c16 : (16 : Int32).toInt = 16 := by decide
  have c2048 : (2048 : Int32).toInt = 2048 := by decide
  have sixteenth := punchmix_div_exact sample 16 (by rw [c16]; decide)
  have quarter : (sample / 16).toInt.natAbs ≤ 32767 := by
    rw [sixteenth.1, c16, Int.natAbs_tdiv]; change sample.toInt.natAbs / 16 ≤ _; omega
  have fits : ((sample / 16).toInt * gain.toInt32.toInt).natAbs < 2 ^ 31 := by
    rw [gv, Int.natAbs_mul]
    calc (sample / 16).toInt.natAbs * (gain.toNat : Int).natAbs ≤ 32767 * 32768 :=
        Nat.mul_le_mul quarter (by rw [Int.natAbs_natCast]; exact unit)
      _ < 2 ^ 31 := by decide
  rw [(punchmix_div_exact _ 2048 (by rw [c2048]; decide)).1, c2048, Int.natAbs_tdiv,
    punchmix_mul_exact _ _ fits, gv, Int.natAbs_mul, sixteenth.1, c16, Int.natAbs_tdiv, Int.natAbs_natCast]
  rfl

/-- The gate never amplifies: with gain at most 32768 (Q15 unity) and a sample within 524287, the output is no
larger than the sample and within 524287. Both divisions truncate toward zero.
Why it matters: a sample inside the limiter's range stays inside it through the gate and cannot wrap. -/
theorem punch_gate_never_amplifies (sample : Int32) (gain : UInt32) (inLimit : sample.toInt.natAbs ≤ 524287)
    (unit : gain.toNat ≤ 32768) :
    (Punch.gateSample sample gain).toInt.natAbs ≤ sample.toInt.natAbs ∧
      (Punch.gateSample sample gain).toInt.natAbs ≤ 524287 := by
  rw [punchmix_gate_size sample gain inLimit unit]
  have step : sample.toInt.natAbs / 16 * gain.toNat / 2048 ≤ sample.toInt.natAbs / 16 * 32768 / 2048 :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ unit)
  have cancel : sample.toInt.natAbs / 16 * 32768 / 2048 = sample.toInt.natAbs / 16 * 16 := by
    rw [show sample.toInt.natAbs / 16 * 32768 = sample.toInt.natAbs / 16 * 16 * 2048 by omega,
      Nat.mul_div_cancel _ (by decide)]
  omega

/-- The crush returns one of its two inputs, so a mix and a held sample both within 524287 give a sample
within 524287.
Why it matters: CRUSH cannot wrap. -/
theorem punch_crush_keeps_limit (factor index : UInt32) (heldSample sample : Int32)
    (h1 : heldSample.toInt.natAbs ≤ 524287) (h2 : sample.toInt.natAbs ≤ 524287) :
    (Punch.crushSample factor index heldSample sample).toInt.natAbs ≤ 524287 := by
  unfold Punch.crushSample
  split <;> assumption

/-- The whole PUNCH audio path keeps the master within 524287, given a mix sample within 524287 (what
`mix_machine_sample_bounded` delivers), a held sample within the same bound, any crush factor and index, and
a gate gain of at most 32768.
Why it matters: with every punch-in on at once, nothing on the PUNCH page can wrap. -/
theorem punch_master_never_wraps (factor index gain : UInt32) (held m : Int32)
    (mixBounded : m.toInt.natAbs ≤ 524287) (heldBounded : held.toInt.natAbs ≤ 524287)
    (unit : gain.toNat ≤ 32768) :
    (Punch.gateSample (Punch.crushSample factor index held m) gain).toInt.natAbs ≤ 524287 :=
  (punch_gate_never_amplifies _ gain
    (punch_crush_keeps_limit factor index held m heldBounded mixBounded) unit).2
