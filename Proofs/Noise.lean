import Firmware.Noise

/-- A 32-bit addition whose true sum fits is exact. -/
private theorem noise_add_exact (a b : Int32) (fits : (a.toInt + b.toInt).natAbs < 2 ^ 31) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A 32-bit subtraction whose true difference fits is exact. -/
private theorem noise_sub_exact (a b : Int32) (fits : (a.toInt - b.toInt).natAbs < 2 ^ 31) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int32.toInt_sub]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A 32-bit product whose true value fits is exact. -/
private theorem noise_mul_exact (a b : Int32) (fits : (a.toInt * b.toInt).natAbs < 2 ^ 31) :
    (a * b).toInt = a.toInt * b.toInt := by
  rw [Int32.toInt_mul]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- The size of a product is at most the product of the sizes. -/
private theorem noise_abs_mul_le (a b : Int) (A B : Nat) (ha : a.natAbs ≤ A) (hb : b.natAbs ≤ B) :
    (a * b).natAbs ≤ A * B := by
  rw [Int.natAbs_mul]; exact Nat.mul_le_mul ha hb

/-- An `Int32` shifted right thirteen places is its value divided by 8192, rounded down. -/
private theorem noise_shift_thirteen (s : Int32) : (s >>> 13).toInt = s.toInt / 8192 := by
  show (s >>> 13).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by fifteen places. -/
private theorem noise_shift_fifteen (s : Int32) : (s >>> 15).toInt = s.toInt / 32768 := by
  show (s >>> 15).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by sixteen places. -/
private theorem noise_shift_sixteen (s : Int32) : (s >>> 16).toInt = s.toInt / 65536 := by
  show (s >>> 16).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by seventeen places. -/
private theorem noise_shift_seventeen (s : Int32) : (s >>> 17).toInt = s.toInt / 131072 := by
  show (s >>> 17).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- Braids' clip as a plain number: the value held between -32767 and 32767. -/
private theorem noise_clip_value (x : Int32) :
    (Digital.clip x).toInt = max (-32767) (min 32767 x.toInt) := by
  unfold Digital.clip
  split
  · rename_i lt; rw [Int32.lt_iff_toInt_lt] at lt; simp at lt ⊢; omega
  · split
    · rename_i _ gt; simp only [gt_iff_lt] at gt; rw [Int32.lt_iff_toInt_lt] at gt; simp at gt ⊢; omega
    · rename_i nlt ngt; simp only [gt_iff_lt] at ngt; rw [Int32.lt_iff_toInt_lt] at nlt ngt
      simp at nlt ngt; omega

/-- A value within 16 bits survives the cut to 16 bits. -/
private theorem noise_keep16 (x : Int32) (lo : -32768 ≤ x.toInt) (hi : x.toInt ≤ 32767) :
    x.toInt16.toInt = x.toInt := by
  rw [Int32.toInt_toInt16]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A `UInt32` below 2^31 keeps its value as an `Int32`. -/
private theorem noise_small_toInt32 (x : UInt32) (below : x.toNat < 2 ^ 31) :
    x.toInt32.toInt = (x.toNat : Int) := by
  show x.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · simp
  · simp at below ⊢; omega

/-- A signed value that is not negative keeps its value as an unsigned one. -/
private theorem noise_toUInt32_of_nonneg (p : Int32) (nonneg : 0 ≤ p.toInt) :
    p.toUInt32.toNat = p.toInt := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- The sine table read, cut to 16 bits in `Analog.sineAt`, is within 16 bits. -/
private theorem noise_sine_fits (phase : UInt32) :
    -32768 ≤ (Analog.sineAt phase).toInt ∧ (Analog.sineAt phase).toInt ≤ 32767 := by
  unfold Analog.sineAt
  rw [Int16.toInt_toInt32]
  generalize Int32.toInt16 _ = x
  have := Int16.toInt_lt x
  have := Int16.le_toInt x
  omega

/-- A 16-bit table entry read as a 32-bit number is between 0 and 65535. -/
private theorem noise_uint16_toInt32 (x : UInt16) : x.toUInt32.toInt32.toInt = (x.toNat : Int) := by
  rw [noise_small_toInt32 _ (by have := x.toNat_lt; simp; omega)]
  simp

/-- Between hits, a particle burst only fades: its amplitude after a sample is at most what it was.
Why it matters: particle noise dies away between hits; the burst cannot grow by itself. -/
theorem noise_particle_amplitude_fades (noise : UInt32) (amplitude : UInt16)
    (s1 c1 s2 c2 s3 c3 y11 y12 y21 y22 y31 y32 : Int32) :
    (Noise.particle noise amplitude s1 c1 s2 c2 s3 c3 y11 y12 y21 y22 y31 y32).amplitude ≤ amplitude := by
  unfold Noise.particle
  dsimp only
  rw [UInt16.le_iff_toNat_le, UInt32.toNat_toUInt16, UInt32.toNat_shiftRight, UInt32.toNat_mul,
    UInt16.toNat_toUInt32]
  have : (UInt32.toNat 16 % 32) = 16 := by decide
  rw [this, Nat.shiftRight_eq_div_pow]
  have := amplitude.toNat_lt
  have k : (64763 : UInt32).toNat = 64763 := by decide
  rw [k]
  have noWrap : amplitude.toNat * 64763 < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt noWrap]
  have : amplitude.toNat * 64763 / 2 ^ 16 ≤ amplitude.toNat := by omega
  rw [Nat.mod_eq_of_lt (by omega)]
  exact this

/-- A signed 16-bit value moved up by 32768 lands on the overdrive curve's 65536 indices.
Why it matters: the filtered and twin-peaks noises read the curve by this index with no bounds check; this
is the condition `tables_shape_reads_inside_257` needs. -/
theorem noise_overdrive_index_in_table (x : Int32) (sixteenBit : -32768 ≤ x.toInt ∧ x.toInt ≤ 32767) :
    (Noise.overdriveIndex x).toNat ≤ 65535 := by
  unfold Noise.overdriveIndex
  have c : (32768 : Int32).toInt = 32768 := by decide
  have sum : (x + 32768).toInt = x.toInt + 32768 := by
    rw [noise_add_exact _ _ (by rw [c]; omega), c]
  have e := noise_toUInt32_of_nonneg _ (by rw [sum]; omega)
  rw [sum] at e
  omega

/-- The filtered noise's gain correction is exact and stays within 16 bits: the mix held between -32767 and
32767, scaled by `gain` parts in 32768, for a gain from 0 to 32767.
Why it matters: the result is the index into the overdrive curve; a wrapped or oversized value would read
outside the curve. -/
theorem noise_corrected_never_wraps (mixed gain : Int32) (gainFits : 0 ≤ gain.toInt ∧ gain.toInt ≤ 32767) :
    (Noise.corrected mixed gain).toInt = max (-32767) (min 32767 mixed.toInt) * gain.toInt / 32768 ∧
      (Noise.corrected mixed gain).toInt.natAbs ≤ 32767 := by
  unfold Noise.corrected
  have c := noise_clip_value mixed
  generalize Digital.clip mixed = m at c
  have small := noise_abs_mul_le m.toInt gain.toInt 32767 32767 (by omega) (by omega)
  rw [noise_shift_fifteen, noise_mul_exact _ _ (by omega), c]
  constructor
  · rfl
  · rw [← c]; omega

/-- The twin peaks' boost is exact: the resonators' sum plus `makeup` parts in 8192 of itself, held between
-32767 and 32767, for a sum within 65536 and a makeup gain from 0 to 8191.
Why it matters: the boost is the last arithmetic before the overdrive curve; it is clipped, not wrapped. -/
theorem noise_boost_never_wraps (sum makeup : Int32) (sumFits : sum.toInt.natAbs ≤ 65536)
    (makeupFits : 0 ≤ makeup.toInt ∧ makeup.toInt ≤ 8191) :
    (Noise.boost sum makeup).toInt =
      max (-32767) (min 32767 (sum.toInt + sum.toInt * makeup.toInt / 8192)) := by
  unfold Noise.boost
  have small := noise_abs_mul_le sum.toInt makeup.toInt 65536 8191 sumFits (by omega)
  have p : ((sum * makeup) >>> 13).toInt = sum.toInt * makeup.toInt / 8192 := by
    rw [noise_shift_thirteen, noise_mul_exact _ _ (by omega)]
  rw [noise_clip_value, noise_add_exact _ _ (by rw [p]; omega), p]

/-- One resonator step is exact: the input scaled by `s` parts in 65536 with its sign kept, plus the last
output times `c` parts in 32768, minus the one before times `q2` parts in 32768, held between -32767 and
32767. Holds for an input within 32768, a scale from 0 to 65535, a coefficient within 65535, a `q2` within
32768 and last outputs within 32767 (they are this step's own clipped results).
Why it matters: the resonators ring the particle and twin-peaks noises; a wrap in the feedback would be a
burst of noise that never decays. -/
theorem noise_resonate_never_wraps (input s c q2 y1 y2 : Int32) (inputFits : input.toInt.natAbs ≤ 32768)
    (sFits : 0 ≤ s.toInt ∧ s.toInt ≤ 65535) (cFits : c.toInt.natAbs ≤ 65535)
    (q2Fits : q2.toInt.natAbs ≤ 32768)
    (y1Fits : y1.toInt.natAbs ≤ 32767) (y2Fits : y2.toInt.natAbs ≤ 32767) :
    (Noise.resonate input s c q2 y1 y2).toInt =
      max (-32767) (min 32767
        ((if 0 < input.toInt then input.toInt * s.toInt / 65536 else -((-input.toInt) * s.toInt / 65536))
          + y1.toInt * c.toInt / 32768 - y2.toInt * q2.toInt / 32768)) := by
  unfold Noise.resonate
  dsimp only
  have zero : (0 : Int32).toInt = 0 := by decide
  have scaled : (if input > 0 then (input * s) >>> 16 else (0 : Int32) - (((0 - input) * s) >>> 16)).toInt =
      if 0 < input.toInt then input.toInt * s.toInt / 65536 else -((-input.toInt) * s.toInt / 65536) := by
    split
    · rename_i pos
      simp only [gt_iff_lt] at pos
      rw [Int32.lt_iff_toInt_lt] at pos
      rw [zero] at pos
      have := noise_abs_mul_le input.toInt s.toInt 32768 65535 inputFits (by omega)
      rw [noise_shift_sixteen, noise_mul_exact _ _ (by omega)]
      split <;> omega
    · rename_i nonpos
      simp only [gt_iff_lt] at nonpos
      rw [Int32.lt_iff_toInt_lt] at nonpos
      rw [zero] at nonpos
      have neg : ((0 : Int32) - input).toInt = -input.toInt := by
        rw [noise_sub_exact _ _ (by rw [zero]; omega), zero]; omega
      have := noise_abs_mul_le (-input.toInt) s.toInt 32768 65535 (by omega) (by omega)
      have p : (((0 - input) * s) >>> 16).toInt = (-input.toInt) * s.toInt / 65536 := by
        rw [noise_shift_sixteen, noise_mul_exact _ _ (by rw [neg]; omega), neg]
      rw [noise_sub_exact _ _ (by rw [zero, p]; omega), zero, p]
      split <;> omega
  generalize (if input > 0 then (input * s) >>> 16 else (0 : Int32) - (((0 - input) * s) >>> 16)) = sc
    at scaled
  generalize hS : (if 0 < input.toInt then input.toInt * s.toInt / 65536
    else -((-input.toInt) * s.toInt / 65536)) = S at scaled
  have sFits' : S.natAbs ≤ 32768 := by
    rw [← hS]
    have := noise_abs_mul_le input.toInt s.toInt 32768 65535 inputFits (by omega)
    have := noise_abs_mul_le (-input.toInt) s.toInt 32768 65535 (by omega) (by omega)
    split <;> omega
  have f1 := noise_abs_mul_le y1.toInt c.toInt 32767 65535 y1Fits cFits
  have f2 := noise_abs_mul_le y2.toInt q2.toInt 32767 32768 y2Fits q2Fits
  have t1 : ((y1 * c) >>> 15).toInt = y1.toInt * c.toInt / 32768 := by
    rw [noise_shift_fifteen, noise_mul_exact _ _ (by omega)]
  have t2 : ((y2 * q2) >>> 15).toInt = y2.toInt * q2.toInt / 32768 := by
    rw [noise_shift_fifteen, noise_mul_exact _ _ (by omega)]
  generalize (y1 * c) >>> 15 = T1 at t1
  generalize (y2 * q2) >>> 15 = T2 at t2
  have sum : (sc + T1).toInt = S + T1.toInt := by
    rw [noise_add_exact _ _ (by rw [scaled]; omega), scaled]
  have diff : (sc + T1 - T2).toInt = S + T1.toInt - T2.toInt := by
    rw [noise_sub_exact _ _ (by rw [sum]; omega), sum]
  rw [noise_clip_value, diff, t1, t2]

/-- A particle burst's sample is exact: the noise word's low 16 bits, read as a signed number, times the
amplitude, divided by 65536, which keeps it within 16 bits.
Why it matters: this is the input to the three resonators; it is within the range they are proved for. -/
theorem noise_burst_never_wraps (noise : UInt32) (amplitude : UInt16) :
    (Noise.burst noise amplitude).toInt = noise.toUInt16.toInt16.toInt * amplitude.toNat / 65536 := by
  unfold Noise.burst
  rw [noise_shift_sixteen, noise_mul_exact, Int16.toInt_toInt32, noise_uint16_toInt32]
  rw [Int16.toInt_toInt32, noise_uint16_toInt32]
  have := Int16.toInt_lt noise.toUInt16.toInt16
  have := Int16.le_toInt noise.toUInt16.toInt16
  have := amplitude.toNat_lt
  have := noise_abs_mul_le noise.toUInt16.toInt16.toInt amplitude.toNat 32768 65535 (by omega) (by omega)
  omega

/-- A resonator's output is clipped, so it is within 16 bits whatever went in. -/
private theorem noise_resonate_fits (input s c q2 y1 y2 : Int32) :
    -32767 ≤ (Noise.resonate input s c q2 y1 y2).toInt ∧
      (Noise.resonate input s c q2 y1 y2).toInt ≤ 32767 := by
  unfold Noise.resonate
  rw [noise_clip_value]
  omega

/-- The particle noise's sample is exact: the three resonators' outputs added and held between -32767 and
32767, with nothing wrapping in the sum.
Why it matters: each resonator is clipped on its own, so the three together need the sum to be clipped
again, not wrapped. -/
theorem noise_particle_never_wraps (noise : UInt32) (amplitude : UInt16)
    (s1 c1 s2 c2 s3 c3 y11 y12 y21 y22 y31 y32 : Int32) :
    (Noise.particle noise amplitude s1 c1 s2 c2 s3 c3 y11 y12 y21 y22 y31 y32).out.toInt =
      max (-32767) (min 32767
        ((Noise.resonate (Noise.burst noise amplitude) s1 c1 32506 y11 y12).toInt
          + (Noise.resonate (Noise.burst noise amplitude) s2 c2 32506 y21 y22).toInt
          + (Noise.resonate (Noise.burst noise amplitude) s3 c3 32506 y31 y32).toInt)) := by
  have shape : (Noise.particle noise amplitude s1 c1 s2 c2 s3 c3 y11 y12 y21 y22 y31 y32).out =
      (Digital.clip (Noise.resonate (Noise.burst noise amplitude) s1 c1 32506 y11 y12
        + Noise.resonate (Noise.burst noise amplitude) s2 c2 32506 y21 y22
        + Noise.resonate (Noise.burst noise amplitude) s3 c3 32506 y31 y32)).toInt16 := rfl
  rw [shape]
  have f1 := noise_resonate_fits (Noise.burst noise amplitude) s1 c1 32506 y11 y12
  have f2 := noise_resonate_fits (Noise.burst noise amplitude) s2 c2 32506 y21 y22
  have f3 := noise_resonate_fits (Noise.burst noise amplitude) s3 c3 32506 y31 y32
  generalize Noise.resonate (Noise.burst noise amplitude) s1 c1 32506 y11 y12 = r1 at f1 ⊢
  generalize Noise.resonate (Noise.burst noise amplitude) s2 c2 32506 y21 y22 = r2 at f2 ⊢
  generalize Noise.resonate (Noise.burst noise amplitude) s3 c3 32506 y31 y32 = r3 at f3 ⊢
  have s12 : (r1 + r2).toInt = r1.toInt + r2.toInt := noise_add_exact _ _ (by omega)
  have s123 : (r1 + r2 + r3).toInt = r1.toInt + r2.toInt + r3.toInt := by
    rw [noise_add_exact _ _ (by rw [s12]; omega), s12]
  rw [noise_keep16 _ (by rw [noise_clip_value]; omega) (by rw [noise_clip_value]; omega), noise_clip_value,
    s123]

/-- The cloud's limiter is exact: the sample is the grains' sum held between -32768 and 32767.
Why it matters: the cloud's sum is cut to 16 bits only after this limit, so the cut changes nothing. -/
theorem noise_cloud_out_never_wraps (sum : Int32) :
    (Noise.cloudOut sum).toInt = max (-32768) (min 32767 sum.toInt) := by
  unfold Noise.cloudOut
  have v : (if sum < -32768 then (-32768 : Int32) else if sum > 32767 then 32767 else sum).toInt =
      max (-32768) (min 32767 sum.toInt) := by
    split
    · rename_i lt; rw [Int32.lt_iff_toInt_lt] at lt; simp at lt ⊢; omega
    · split
      · rename_i _ gt; simp only [gt_iff_lt] at gt; rw [Int32.lt_iff_toInt_lt] at gt; simp at gt ⊢; omega
      · rename_i nlt ngt; simp only [gt_iff_lt] at ngt; rw [Int32.lt_iff_toInt_lt] at nlt ngt
        simp at nlt ngt; omega
  rw [noise_keep16 _ (by rw [v]; omega) (by rw [v]; omega), v]

/-- A grain's share of the sample is exact: the sine at its new phase times its envelope entry, divided by
131072, which is within 16384 either way, so the cloud's limiter sees the exact sum of its four grains.
Why it matters: the cloud adds four of these for every sample; a wrapped share would be a click. -/
theorem noise_grain_never_wraps (phase inc envelope envInc : UInt32) :
    (Noise.grain phase inc envelope envInc).contribution.toInt =
      (Analog.sineAt (phase + inc)).toInt * (Noise.grainEnvelope ((envelope + envInc) >>> 16)).toNat
        / 131072 ∧
      (Noise.grain phase inc envelope envInc).contribution.toInt.natAbs ≤ 16384 := by
  unfold Noise.grain
  dsimp only
  have sine := noise_sine_fits (phase + inc)
  have env := (Noise.grainEnvelope ((envelope + envInc) >>> 16)).toNat_lt
  rw [noise_shift_seventeen, noise_mul_exact, noise_uint16_toInt32]
  · have := noise_abs_mul_le (Analog.sineAt (phase + inc)).toInt
      (Noise.grainEnvelope ((envelope + envInc) >>> 16)).toNat 32768 65535 (by omega) (by omega)
    omega
  · rw [noise_uint16_toInt32]
    have := noise_abs_mul_le (Analog.sineAt (phase + inc)).toInt
      (Noise.grainEnvelope ((envelope + envInc) >>> 16)).toNat 32768 65535 (by omega) (by omega)
    omega

/-- A grain reads inside its 513-entry envelope as long as its envelope phase is at or below 2^24 + 2^22 and
its rate is at most 2^18 per sample. Both come from the block's setup (`noise_setup_grain_reset`): a grain
starts at 0 and a block of up to 16 samples at that rate cannot carry an envelope that was still playing
past that point.
Why it matters: the envelope is a plain C array read without a bounds check. -/
theorem noise_grain_envelope_index_in_table (phase inc envelope envInc : UInt32)
    (started : envelope.toNat ≤ 2 ^ 24 + 2 ^ 22) (rate : envInc.toNat ≤ 2 ^ 18) :
    ((Noise.grain phase inc envelope envInc).envelope >>> 16).toNat ≤ 512 := by
  unfold Noise.grain
  dsimp only
  rw [UInt32.toNat_shiftRight, UInt32.toNat_add]
  have : (UInt32.toNat 16 % 32) = 16 := by decide
  rw [this, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
  omega
