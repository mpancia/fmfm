import Firmware.Mix

/-!
The mix in `dinghy.c`: the level glide of a voice, its sample, its share for the reverb bus, and the wet
return, with the limits the firmware keeps: a gate of at most 130048 (`play`), a gain of at most 2048
(`tools/gen_presets.py`), a send of at most 256, a return gain of at most 65500, six voices.
-/

/-- A 32-bit sum whose true value fits is exact. -/
private theorem mix_add_exact (a b : Int32) (fits : (a.toInt + b.toInt).natAbs < 2 ^ 31) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A 32-bit difference whose true value fits is exact. -/
private theorem mix_sub_exact (a b : Int32) (fits : (a.toInt - b.toInt).natAbs < 2 ^ 31) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int32.toInt_sub]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A 32-bit product whose true value fits is exact. -/
private theorem mix_mul_exact (a b : Int32) (fits : (a.toInt * b.toInt).natAbs < 2 ^ 31) :
    (a * b).toInt = a.toInt * b.toInt := by
  rw [Int32.toInt_mul]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- An arithmetic shift right of a 32-bit number by 4 is division by 16, rounding down. -/
private theorem mix_shift4 (x : Int32) : (x >>> 4).toInt = x.toInt / 16 := by
  show (x >>> 4).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by 8. -/
private theorem mix_shift8 (x : Int32) : (x >>> 8).toInt = x.toInt / 256 := by
  show (x >>> 8).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by 15. -/
private theorem mix_shift15 (x : Int32) : (x >>> 15).toInt = x.toInt / 32768 := by
  show (x >>> 15).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same for a 64-bit number shifted by 15. -/
private theorem mix_shift64 (x : Int64) : (x >>> 15).toInt = x.toInt / 32768 := by
  show (x >>> 15).toBitVec.toInt = _
  rw [Int64.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- A 16-bit unsigned value keeps its value as a 32-bit signed one. -/
private theorem mix_uint16_toInt (g : UInt16) : g.toUInt32.toInt32.toInt = g.toNat := by
  show g.toUInt32.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · simp
  · have := UInt16.toNat_lt g; simp; omega

/-- A product of a value within `a` and a value between 0 and `b` is within `a * b`. -/
private theorem mix_product_bound (s t : Int) (a b : Nat) (hs : s.natAbs ≤ a) (nonneg : 0 ≤ t) (ht : t ≤ b) :
    (s * t).natAbs ≤ a * b := by
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul hs (by omega)

/-- The level of a voice one sample later lies between where it was and its gate, and so stays between 0
and 130048 (the top of `play`'s gate). The steps are `ATTACK` (at most 1024) and `RELEASE` (at most 250).
Why it matters: the glide that removes clicks cannot overshoot and bounce, and the level never wraps to a
negative number that would flip the sound's sign or make a released voice sound again. -/
theorem mix_envelope_toward_gate (amp gate up down : Int32)
    (ampInRange : 0 ≤ amp.toInt ∧ amp.toInt ≤ 130048) (gateInRange : 0 ≤ gate.toInt ∧ gate.toInt ≤ 130048)
    (upInRange : 0 ≤ up.toInt ∧ up.toInt ≤ 1024) (downInRange : 0 ≤ down.toInt ∧ down.toInt ≤ 250) :
    min amp.toInt gate.toInt ≤ (Mix.envelopeStep amp gate up down).toInt ∧
      (Mix.envelopeStep amp gate up down).toInt ≤ max amp.toInt gate.toInt ∧
      0 ≤ (Mix.envelopeStep amp gate up down).toInt ∧ (Mix.envelopeStep amp gate up down).toInt ≤ 130048 := by
  unfold Mix.envelopeStep
  have raised := mix_add_exact amp up (by omega)
  have lowered := mix_sub_exact amp down (by omega)
  dsimp only
  split <;> (try split) <;> (try split) <;>
    simp only [gt_iff_lt, Int32.lt_iff_toInt_lt, raised, lowered] at * <;> omega

/-- The product of a Braids sample and a gain of at most 2048 fits in 32 bits. -/
private theorem mix_gain_product (sample : Int16) (gain : UInt16) (gainInRange : gain.toNat ≤ 2048) :
    (sample.toInt32 * gain.toUInt32.toInt32).toInt = sample.toInt * gain.toNat := by
  have lo := Int16.le_toInt sample
  have hi := Int16.toInt_lt sample
  rw [mix_mul_exact, Int16.toInt_toInt32, mix_uint16_toInt]
  rw [Int16.toInt_toInt32, mix_uint16_toInt]
  have := mix_product_bound sample.toInt gain.toNat 32768 2048 (by omega) (by omega) (by omega)
  omega

/-- A voice's sample as a plain number, and its bound. -/
private theorem mix_voice_value (sample : Int16) (gain : UInt16) (amp : Int32)
    (gainInRange : gain.toNat ≤ 2048) (ampInRange : 0 ≤ amp.toInt ∧ amp.toInt ≤ 130048) :
    (Mix.voiceSample sample gain amp).toInt =
        sample.toInt * gain.toNat / 256 * (amp.toInt / 16) / 32768 ∧
      (Mix.voiceSample sample gain amp).toInt.natAbs ≤ 65024 := by
  have lo := Int16.le_toInt sample
  have hi := Int16.toInt_lt sample
  have scaled : ((sample.toInt32 * gain.toUInt32.toInt32) >>> 8).toInt = sample.toInt * gain.toNat / 256 := by
    rw [mix_shift8, mix_gain_product sample gain gainInRange]
  have scaledBound : (sample.toInt * gain.toNat / 256).natAbs ≤ 262144 := by
    have := mix_product_bound sample.toInt gain.toNat 32768 2048 (by omega) (by omega) (by omega)
    omega
  have productBound := mix_product_bound (sample.toInt * gain.toNat / 256) (amp.toInt / 16) 262144 8128
    scaledBound (by omega) (by omega)
  have product : (((sample.toInt32 * gain.toUInt32.toInt32) >>> 8) * (amp >>> 4)).toInt =
      sample.toInt * gain.toNat / 256 * (amp.toInt / 16) := by
    rw [mix_mul_exact, scaled, mix_shift4]
    rw [scaled, mix_shift4]
    omega
  unfold Mix.voiceSample
  rw [mix_shift15, product]
  omega

/-- The share for the reverb bus of a sample within 65024 is within 130048 when `send` is at most 256. -/
private theorem mix_send_value (s : Int32) (send : UInt16) (sBounded : s.toInt.natAbs ≤ 65024)
    (sendInRange : send.toNat ≤ 256) : (Mix.sendSample s send).toInt.natAbs ≤ 130048 := by
  have two : (2 : Int32).toInt = 2 := by decide
  have doubled : (s * 2).toInt = s.toInt * 2 := by
    rw [mix_mul_exact, two]; rw [two]; omega
  have sentBound := mix_product_bound (s.toInt * 2) send.toNat 130048 256 (by omega) (by omega) (by omega)
  have sent : (s * 2 * send.toUInt32.toInt32).toInt = s.toInt * 2 * send.toNat := by
    rw [mix_mul_exact, doubled, mix_uint16_toInt]
    rw [doubled, mix_uint16_toInt]
    omega
  unfold Mix.sendSample
  rw [mix_shift8, sent]
  omega

/-- A voice's sample for the mix is computed without any wrap, given a gain of at most 2048 (the most
`tools/gen_presets.py` writes) and a level of at most 130048, and it is within 65024 either way; the share
sent to the reverb bus (send at most 256) is within 130048.
Why it matters: the loudest voice at the loudest gain stays an exact scaled copy of what Braids rendered,
never a wrapped burst, and six of each fit the stereo mix and the send bus with room to spare. -/
theorem mix_voice_sample_never_wraps (sample : Int16) (gain send : UInt16) (amp : Int32)
    (gainInRange : gain.toNat ≤ 2048) (sendInRange : send.toNat ≤ 256)
    (ampInRange : 0 ≤ amp.toInt ∧ amp.toInt ≤ 130048) :
    (Mix.voiceSample sample gain amp).toInt =
        sample.toInt * gain.toNat / 256 * (amp.toInt / 16) / 32768 ∧
      (Mix.voiceSample sample gain amp).toInt.natAbs ≤ 65024 ∧
      (Mix.sendSample (Mix.voiceSample sample gain amp) send).toInt.natAbs ≤ 130048 := by
  have value := mix_voice_value sample gain amp gainInRange ampInRange
  exact ⟨value.1, value.2, mix_send_value _ send value.2 sendInRange⟩

/-- Adding voice samples within 65024 each to a running total is exact while the total fits, and the total
grows by at most 65024 a voice. -/
private theorem mix_dry_sum (voices : List Int32) (acc : Int32)
    (eachBounded : ∀ s ∈ voices, s.toInt.natAbs ≤ 65024)
    (fits : acc.toInt.natAbs + 65024 * voices.length < 2 ^ 31) :
    (voices.foldl (· + ·) acc).toInt = acc.toInt + (voices.map Int32.toInt).sum ∧
      (voices.foldl (· + ·) acc).toInt.natAbs ≤ acc.toInt.natAbs + 65024 * voices.length := by
  induction voices generalizing acc with
  | nil => simp
  | cons s rest ih =>
    have sBound := eachBounded s (by simp)
    have restBounded : ∀ t ∈ rest, t.toInt.natAbs ≤ 65024 := fun t ht => eachBounded t (by simp [ht])
    simp only [List.length_cons] at fits
    have step := mix_add_exact acc s (by omega)
    have := ih (acc + s) restBounded (by rw [step]; omega)
    rw [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [step] at this
    simp only [List.length_cons]
    omega

/-- The wet return is computed without any wrap and is within 2096000, given a wet sample within 2^20 and a
return gain of at most 65500. -/
private theorem mix_wet_return (wet gain : Int32) (wetBounded : wet.toInt.natAbs ≤ 2 ^ 20)
    (returnInRange : 0 ≤ gain.toInt ∧ gain.toInt ≤ 65500) :
    (Mix.wetSample wet gain).toInt = wet.toInt * gain.toInt / 32768 ∧
      (Mix.wetSample wet gain).toInt.natAbs ≤ 2096000 := by
  unfold Mix.wetSample
  have := mix_product_bound wet.toInt gain.toInt (2 ^ 20) 65500 wetBounded (by omega) (by omega)
  have product : (wet.toInt64 * gain.toInt64).toInt = wet.toInt * gain.toInt := by
    rw [Int64.toInt_mul, Int32.toInt_toInt64, Int32.toInt_toInt64]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  rw [Int64.toInt_toInt32, mix_shift64, product]
  rw [Int.bmod_eq_of_le (by omega) (by omega)]
  omega

/-- The stereo mix of up to six voice samples (each within 65024, as `mix_voice_sample_never_wraps` gives)
plus the wet return is added up without any wrap: the dry sum is within 390144, the whole within 2486144.
The wet sample is taken to be within 2^20, four times the loudest value the reverb memory can hold.
The last conjunct is for `platform.c`, which multiplies the mix by the master gain (at most 4088, Q12)
before its clip to 16 bits: the dry mix cannot wrap in that product either.
Why it matters: six loud voices together can only clip at the deliberate clip in `platform.c`, never wrap
in the mix to a burst of the opposite sign. -/
theorem mix_bus_never_wraps (voices : List Int32) (wet gain : Int32) (atMostSix : voices.length ≤ 6)
    (eachBounded : ∀ s ∈ voices, s.toInt.natAbs ≤ 65024) (wetBounded : wet.toInt.natAbs ≤ 2 ^ 20)
    (returnInRange : 0 ≤ gain.toInt ∧ gain.toInt ≤ 65500) :
    (voices.foldl (· + ·) 0).toInt = (voices.map Int32.toInt).sum ∧
      (voices.foldl (· + ·) 0).toInt.natAbs ≤ 390144 ∧
      (voices.foldl (· + ·) 0 + Mix.wetSample wet gain).toInt =
        (voices.map Int32.toInt).sum + wet.toInt * gain.toInt / 32768 ∧
      (voices.foldl (· + ·) 0 + Mix.wetSample wet gain).toInt.natAbs ≤ 2486144 ∧
      (voices.foldl (· + ·) 0).toInt.natAbs * 4088 < 2 ^ 31 := by
  have zero : (0 : Int32).toInt = 0 := by decide
  have dry := mix_dry_sum voices 0 eachBounded (by rw [zero]; simp; omega)
  have wetReturn := mix_wet_return wet gain wetBounded returnInRange
  rw [zero] at dry
  have total := mix_add_exact (voices.foldl (· + ·) 0) (Mix.wetSample wet gain) (by omega)
  rw [total, dry.1, wetReturn.1]
  omega

/-- After the limiter the mix is within 524287, so `platform.c`'s product with the master gain (at most 4088)
fits in 32 bits for any input; and a mix already within that range passes through unchanged.
Why it matters: the dry mix never reaches the limit (`mix_bus_never_wraps`), so the limiter only acts on an
extreme wet return, where it keeps the master stage from wrapping to a burst of the opposite sign. -/
theorem mix_limit_fits_master (x : Int32) :
    (Mix.limit x).toInt.natAbs * 4088 < 2 ^ 31 ∧ (x.toInt.natAbs ≤ 524287 → Mix.limit x = x) := by
  have hi : (524287 : Int32).toInt = 524287 := by decide
  have lo : (-524287 : Int32).toInt = -524287 := by decide
  unfold Mix.limit
  constructor
  · split
    · rw [hi]; decide
    · split
      · rw [lo]; decide
      · rename_i notHigh notLow
        rw [Int32.not_lt, Int32.le_iff_toInt_le, hi] at notHigh
        rw [Int32.not_lt, Int32.le_iff_toInt_le, lo] at notLow
        omega
  · intro small
    rw [ite_eq_right, ite_eq_right]
    · rw [Int32.not_lt, Int32.le_iff_toInt_le, lo]; omega
    · rw [Int32.not_lt, Int32.le_iff_toInt_le, hi]; omega
