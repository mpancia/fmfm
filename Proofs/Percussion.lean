import Firmware.Percussion

/-- A 32-bit addition whose true sum fits is exact. -/
private theorem percussion_add_exact (a b : Int32) (fits : (a.toInt + b.toInt).natAbs < 2 ^ 31) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A 32-bit subtraction whose true difference fits is exact. -/
private theorem percussion_sub_exact (a b : Int32) (fits : (a.toInt - b.toInt).natAbs < 2 ^ 31) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int32.toInt_sub]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A 32-bit product whose true value fits is exact. -/
private theorem percussion_mul_exact (a b : Int32) (fits : (a.toInt * b.toInt).natAbs < 2 ^ 31) :
    (a * b).toInt = a.toInt * b.toInt := by
  rw [Int32.toInt_mul]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- The size of a product is at most the product of the sizes. -/
private theorem percussion_abs_mul_le (a b : Int) (A B : Nat) (ha : a.natAbs ≤ A) (hb : b.natAbs ≤ B) :
    (a * b).natAbs ≤ A * B := by
  rw [Int.natAbs_mul]; exact Nat.mul_le_mul ha hb

/-- An `Int32` shifted right four places is its value divided by 16, rounded down. -/
private theorem percussion_shift_four (s : Int32) : (s >>> 4).toInt = s.toInt / 16 := by
  show (s >>> 4).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by seven places. -/
private theorem percussion_shift_seven (s : Int32) : (s >>> 7).toInt = s.toInt / 128 := by
  show (s >>> 7).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by eight places. -/
private theorem percussion_shift_eight (s : Int32) : (s >>> 8).toInt = s.toInt / 256 := by
  show (s >>> 8).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by nine places. -/
private theorem percussion_shift_nine (s : Int32) : (s >>> 9).toInt = s.toInt / 512 := by
  show (s >>> 9).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by fourteen places. -/
private theorem percussion_shift_fourteen (s : Int32) : (s >>> 14).toInt = s.toInt / 16384 := by
  show (s >>> 14).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by fifteen places. -/
private theorem percussion_shift_fifteen (s : Int32) : (s >>> 15).toInt = s.toInt / 32768 := by
  show (s >>> 15).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by sixteen places. -/
private theorem percussion_shift_sixteen (s : Int32) : (s >>> 16).toInt = s.toInt / 65536 := by
  show (s >>> 16).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by seventeen places. -/
private theorem percussion_shift_seventeen (s : Int32) : (s >>> 17).toInt = s.toInt / 131072 := by
  show (s >>> 17).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- Braids' clip as a plain number: the value held between -32767 and 32767. -/
private theorem percussion_clip_value (x : Int32) :
    (Digital.clip x).toInt = max (-32767) (min 32767 x.toInt) := by
  unfold Digital.clip
  split
  · rename_i lt; rw [Int32.lt_iff_toInt_lt] at lt; simp at lt ⊢; omega
  · split
    · rename_i _ gt; simp only [gt_iff_lt] at gt; rw [Int32.lt_iff_toInt_lt] at gt; simp at gt ⊢; omega
    · rename_i nlt ngt; simp only [gt_iff_lt] at ngt; rw [Int32.lt_iff_toInt_lt] at nlt ngt
      simp at nlt ngt; omega

/-- A value within 16 bits survives the cut to 16 bits. -/
private theorem percussion_keep16 (x : Int32) (lo : -32768 ≤ x.toInt) (hi : x.toInt ≤ 32767) :
    x.toInt16.toInt = x.toInt := by
  rw [Int32.toInt_toInt16]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- The sine table read, cut to 16 bits in `Analog.sineAt`, is within 16 bits. -/
private theorem percussion_sine_fits (phase : UInt32) :
    -32768 ≤ (Analog.sineAt phase).toInt ∧ (Analog.sineAt phase).toInt ≤ 32767 := by
  unfold Analog.sineAt
  rw [Int16.toInt_toInt32]
  generalize Int32.toInt16 _ = x
  have := Int16.toInt_lt x
  have := Int16.le_toInt x
  omega

/-- Moving from `a` toward `b` by `t` parts in `N` (`0 ≤ t ≤ N`) lands between the two. -/
private theorem percussion_between (a b t N : Int) (pos : 0 < N) (ht : 0 ≤ t ∧ t ≤ N) :
    min a b ≤ a + (b - a) * t / N ∧ a + (b - a) * t / N ≤ max a b := by
  by_cases h : 0 ≤ b - a
  · have u : (b - a) * t ≤ (b - a) * N := Int.mul_le_mul_of_nonneg_left ht.2 h
    have l : 0 ≤ (b - a) * t := Int.mul_nonneg h ht.1
    have u' := Int.ediv_le_ediv pos u
    rw [Int.mul_ediv_cancel _ (by omega)] at u'
    have l' := Int.ediv_nonneg l (by omega : (0 : Int) ≤ N)
    omega
  · have neg : b - a ≤ 0 := by omega
    have l : (b - a) * N ≤ (b - a) * t := Int.mul_le_mul_of_nonpos_left neg ht.2
    have u : (b - a) * t ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg neg ht.1
    have l' := Int.ediv_le_ediv pos l
    rw [Int.mul_ediv_cancel _ (by omega)] at l'
    have u' := Int.ediv_nonpos_of_nonpos_of_neg u pos
    omega

/-- A signed value between 0 and 2^19 keeps its value as an unsigned one. -/
private theorem percussion_small_toUInt32 (p : Int32) (lo : 0 ≤ p.toInt) (hi : p.toInt ≤ 524288) :
    p.toUInt32.toNat = p.toInt := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- A `UInt32` below 2^31 keeps its value when read as an `Int32`. -/
private theorem percussion_uint32_toInt32_toInt (x : UInt32) (below : x.toNat < 2 ^ 31) :
    x.toInt32.toInt = (x.toNat : Int) := by
  show x.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · simp
  · simp at below ⊢; omega

/-- Between hits an exciter's pulse stays at or below where it was and never below zero, for a pulse at most
2^19 (the loudest strike is 15 times 32768) and a decay at most 4096 (one, in 12 bits).
Why it matters: the exciter cannot grow on its own or go negative. -/
theorem percussion_excite_decays (state decay counter level : Int32)
    (nonneg : 0 ≤ state.toInt) (small : state.toInt ≤ 524288) (gentle : 0 ≤ decay.toInt ∧ decay.toInt ≤ 4096)
    (quiet : counter.toInt ≠ 1) :
    0 ≤ (Percussion.excite state decay counter level).state.toInt ∧
      (Percussion.excite state decay counter level).state.toInt ≤ state.toInt := by
  unfold Percussion.excite
  dsimp only
  have notFired : (counter > 0 && (if counter > 0 then counter - 1 else counter) == 0) = false := by
    by_cases h : counter > 0
    · simp only [h, decide_true, Bool.true_and, ite_true]
      rw [beq_eq_false_iff_ne]
      intro bad
      apply quiet
      have := congrArg Int32.toInt bad
      rw [Int32.toInt_sub] at this
      simp [Int.bmod_def] at this
      have r := Int32.toInt_lt counter
      have l := Int32.le_iff_toInt_le.mp (Int32.minValue_le counter)
      rw [Int32.toInt_minValue] at l
      split at this <;> omega
    · simp [h]
  rw [notFired]
  simp only [Bool.false_eq_true, ite_false]
  have sv := percussion_small_toUInt32 state nonneg small
  have dv := percussion_small_toUInt32 decay gentle.1 (by omega)
  have product : (state.toUInt32 * decay.toUInt32).toNat = state.toUInt32.toNat * decay.toUInt32.toNat := by
    rw [UInt32.toNat_mul, Nat.mod_eq_of_lt]
    have a : state.toUInt32.toNat ≤ 524288 := by omega
    have b : decay.toUInt32.toNat ≤ 4096 := by omega
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul a b) (by decide)
  have shifted : ((state.toUInt32 * decay.toUInt32) >>> 12).toNat =
      state.toUInt32.toNat * decay.toUInt32.toNat / 4096 := by
    rw [UInt32.toNat_shiftRight, product]
    have : (UInt32.toNat 12 % 32) = 12 := by decide
    rw [this, Nat.shiftRight_eq_div_pow]
  have le : state.toUInt32.toNat * decay.toUInt32.toNat / 4096 ≤ state.toUInt32.toNat := by
    have b : decay.toUInt32.toNat ≤ 4096 := by omega
    have := Nat.mul_le_mul_left state.toUInt32.toNat b
    omega
  rw [percussion_uint32_toInt32_toInt _ (by omega), shifted]
  omega

/-- Between blocks a partial's new amplitude is at least zero and at most what it was, for an amplitude up to
32767, decays up to 65535 (the short one at most the long one) and any setting from 0 to 32767.
Why it matters: the decay cannot make a partial louder or flip its sign, so amplitudes stay in the range
the partial arithmetic is proved for. -/
theorem percussion_decay_never_grows (amplitude decayLong decayShort parameter : Int32)
    (amplitudeFits : 0 ≤ amplitude.toInt ∧ amplitude.toInt ≤ 32767)
    (decayFits : 0 ≤ decayShort.toInt ∧ decayShort.toInt ≤ decayLong.toInt ∧ decayLong.toInt ≤ 65535)
    (parameterFits : 0 ≤ parameter.toInt ∧ parameter.toInt ≤ 32767) :
    0 ≤ (Percussion.decay amplitude decayLong decayShort parameter).toInt ∧
      (Percussion.decay amplitude decayLong decayShort parameter).toInt ≤ amplitude.toInt := by
  unfold Percussion.decay
  dsimp only
  have c32767 : (32767 : Int32).toInt = 32767 := by decide
  have sub : ((32767 : Int32) - parameter).toInt = 32767 - parameter.toInt := by
    rw [percussion_sub_exact _ _ (by rw [c32767]; omega), c32767]
  have b0 : (((32767 : Int32) - parameter) >>> 8).toInt16.toInt32.toInt =
      (32767 - parameter.toInt) / 256 := by
    rw [Int16.toInt_toInt32, percussion_keep16 _ (by rw [percussion_shift_eight, sub]; omega)
      (by rw [percussion_shift_eight, sub]; omega), percussion_shift_eight, sub]
  generalize ((32767 : Int32) - parameter) >>> 8 = b0v at b0
  generalize hB0 : (32767 - parameter.toInt) / 256 = B0 at b0
  have b0Fits : 0 ≤ B0 ∧ B0 ≤ 127 := by omega
  have sq : (b0v.toInt16.toInt32 * b0v.toInt16.toInt32).toInt = B0 * B0 := by
    have := percussion_abs_mul_le B0 B0 127 127 (by omega) (by omega)
    rw [percussion_mul_exact _ _ (by rw [b0]; omega), b0]
  have sqFits : 0 ≤ B0 * B0 ∧ B0 * B0 ≤ 16129 := by
    have := Int.mul_le_mul b0Fits.2 b0Fits.2 b0Fits.1 (by omega)
    have := Int.mul_nonneg b0Fits.1 b0Fits.1
    omega
  have balance : ((b0v.toInt16.toInt32 * b0v.toInt16.toInt32) >>> 7).toInt16.toInt32.toInt =
      B0 * B0 / 128 := by
    rw [Int16.toInt_toInt32, percussion_keep16 _ (by rw [percussion_shift_seven, sq]; omega)
      (by rw [percussion_shift_seven, sq]; omega), percussion_shift_seven, sq]
  generalize ((b0v.toInt16.toInt32 * b0v.toInt16.toInt32) >>> 7).toInt16.toInt32 = bal at balance
  generalize hBAL : B0 * B0 / 128 = BAL at balance
  have balFits : 0 ≤ BAL ∧ BAL ≤ 126 := by omega
  have dd : (decayLong - decayShort).toInt = decayLong.toInt - decayShort.toInt :=
    percussion_sub_exact _ _ (by omega)
  have prod : ((decayLong - decayShort) * bal).toInt = (decayLong.toInt - decayShort.toInt) * BAL := by
    have := percussion_abs_mul_le (decayLong.toInt - decayShort.toInt) BAL 65535 126 (by omega) (by omega)
    rw [percussion_mul_exact _ _ (by rw [dd, balance]; omega), dd, balance]
  have prodFits : 0 ≤ (decayLong.toInt - decayShort.toInt) * BAL ∧
      (decayLong.toInt - decayShort.toInt) * BAL ≤ (decayLong.toInt - decayShort.toInt) * 126 := by
    constructor
    · exact Int.mul_nonneg (by omega) balFits.1
    · exact Int.mul_le_mul_of_nonneg_left balFits.2 (by omega)
  have d : (decayLong - (((decayLong - decayShort) * bal) >>> 7)).toInt =
      decayLong.toInt - (decayLong.toInt - decayShort.toInt) * BAL / 128 := by
    rw [percussion_sub_exact _ _ (by rw [percussion_shift_seven, prod]; omega), percussion_shift_seven, prod]
  generalize decayLong - (((decayLong - decayShort) * bal) >>> 7) = dv at d
  generalize hD : decayLong.toInt - (decayLong.toInt - decayShort.toInt) * BAL / 128 = D at d
  have dFits : 0 ≤ D ∧ D ≤ 65535 := by omega
  have final : (amplitude * dv).toInt = amplitude.toInt * D := by
    have := percussion_abs_mul_le amplitude.toInt D 32767 65535 (by omega) (by omega)
    rw [percussion_mul_exact _ _ (by rw [d]; omega), d]
  rw [percussion_shift_sixteen, final]
  have := Int.mul_le_mul_of_nonneg_left dFits.2 amplitudeFits.1
  have := Int.mul_nonneg amplitudeFits.1 dFits.1
  omega

/-- A bell partial's share of the sample is exact: the sine at its new phase times its amplitude, divided by
131072, for an amplitude from 0 to 32767 (Braids' bell partials start at most at 21872 and only decay).
Why it matters: eleven of these are added every sample of a bell; a wrapped share would be a click. -/
theorem percussion_bell_partial_never_wraps (phase inc : UInt32) (amplitude : Int32)
    (amplitudeFits : 0 ≤ amplitude.toInt ∧ amplitude.toInt ≤ 32767) :
    (Percussion.bellPartial phase inc amplitude).contribution.toInt =
      (Analog.sineAt (phase + inc)).toInt * amplitude.toInt / 131072 := by
  unfold Percussion.bellPartial
  dsimp only
  have sine := percussion_sine_fits (phase + inc)
  have := percussion_abs_mul_le (Analog.sineAt (phase + inc)).toInt amplitude.toInt 32768 32767 (by omega)
    (by omega)
  rw [percussion_shift_seventeen, percussion_mul_exact _ _ (by omega)]

/-- A drum partial's share of the sample is exact: the amplitude moves from `amplitude` toward `target` by
`fade` parts in 32768, and the sine at its new phase times that, divided by 65536, is the share. Holds for
amplitudes from 0 to 32767 (Braids' drum partials start at most at 16986) and a fade from 0 to 32768.
Why it matters: six of these are added every sample of a drum; a wrapped share would be a click. -/
theorem percussion_drum_partial_never_wraps (phase inc : UInt32) (amplitude target fade : Int32)
    (amplitudeFits : 0 ≤ amplitude.toInt ∧ amplitude.toInt ≤ 32767)
    (targetFits : 0 ≤ target.toInt ∧ target.toInt ≤ 32767) (fadeFits : 0 ≤ fade.toInt ∧ fade.toInt ≤ 32768) :
    (Percussion.drumPartial phase inc amplitude target fade).contribution.toInt =
      (Analog.sineAt (phase + inc)).toInt *
        (amplitude.toInt + (target.toInt - amplitude.toInt) * fade.toInt / 32768) / 65536 := by
  unfold Percussion.drumPartial
  dsimp only
  have d : (target - amplitude).toInt = target.toInt - amplitude.toInt := percussion_sub_exact _ _ (by omega)
  have small := percussion_abs_mul_le (target.toInt - amplitude.toInt) fade.toInt 32767 32768 (by omega)
    (by omega)
  have p : ((target - amplitude) * fade).toInt = (target.toInt - amplitude.toInt) * fade.toInt := by
    rw [percussion_mul_exact _ _ (by rw [d]; omega), d]
  have between := percussion_between amplitude.toInt target.toInt fade.toInt 32768 (by decide) fadeFits
  have a : (amplitude + (((target - amplitude) * fade) >>> 15)).toInt =
      amplitude.toInt + (target.toInt - amplitude.toInt) * fade.toInt / 32768 := by
    rw [percussion_add_exact _ _ (by rw [percussion_shift_fifteen, p]; omega), percussion_shift_fifteen, p]
  generalize amplitude + (((target - amplitude) * fade) >>> 15) = av at a
  generalize hA : amplitude.toInt + (target.toInt - amplitude.toInt) * fade.toInt / 32768 = A at a between
  have sine := percussion_sine_fits (phase + inc)
  have := percussion_abs_mul_le (Analog.sineAt (phase + inc)).toInt A 32768 32767 (by omega) (by omega)
  rw [percussion_shift_sixteen, percussion_mul_exact _ _ (by rw [a]; omega), a]

/-- The snare's sample is exact: the two filtered exciters, each with a sixteenth of its raw pulse, at their
gains, plus the filtered noise, clipped to ±32767. Holds for 16-bit filter outputs and noise, a first pulse
within 2^19 and a second within 2^18 (Braids strikes them at 15 times 32768 and at 13107) and the gains
Braids uses (22000 minus and plus half the first parameter).
Why it matters: the sum of three loud signals clips, not wraps. -/
theorem percussion_snare_never_wraps (filtered1 excitation1 filtered2 excitation2 noise g1 g2 : Int32)
    (filtered1Fits : filtered1.toInt.natAbs ≤ 32767) (excitation1Fits : excitation1.toInt.natAbs ≤ 2 ^ 19)
    (filtered2Fits : filtered2.toInt.natAbs ≤ 32767) (excitation2Fits : excitation2.toInt.natAbs ≤ 2 ^ 18)
    (noiseFits : noise.toInt.natAbs ≤ 32767)
    (g1Fits : 0 ≤ g1.toInt ∧ g1.toInt ≤ 22000) (g2Fits : 0 ≤ g2.toInt ∧ g2.toInt ≤ 38383) :
    (Percussion.snareMix filtered1 excitation1 filtered2 excitation2 noise g1 g2).toInt =
      max (-32767) (min 32767
        ((filtered1.toInt + excitation1.toInt / 16) * g1.toInt / 32768
          + (filtered2.toInt + excitation2.toInt / 16) * g2.toInt / 32768 + noise.toInt)) := by
  unfold Percussion.snareMix
  have s1 : (filtered1 + (excitation1 >>> 4)).toInt = filtered1.toInt + excitation1.toInt / 16 := by
    rw [percussion_add_exact _ _ (by rw [percussion_shift_four]; omega), percussion_shift_four]
  have s2 : (filtered2 + (excitation2 >>> 4)).toInt = filtered2.toInt + excitation2.toInt / 16 := by
    rw [percussion_add_exact _ _ (by rw [percussion_shift_four]; omega), percussion_shift_four]
  have m1 := percussion_abs_mul_le (filtered1.toInt + excitation1.toInt / 16) g1.toInt 65535 22000 (by omega)
    (by omega)
  have m2 := percussion_abs_mul_le (filtered2.toInt + excitation2.toInt / 16) g2.toInt 49151 38383 (by omega)
    (by omega)
  have p1 : (((filtered1 + (excitation1 >>> 4)) * g1) >>> 15).toInt =
      (filtered1.toInt + excitation1.toInt / 16) * g1.toInt / 32768 := by
    rw [percussion_shift_fifteen, percussion_mul_exact _ _ (by rw [s1]; omega), s1]
  have p2 : (((filtered2 + (excitation2 >>> 4)) * g2) >>> 15).toInt =
      (filtered2.toInt + excitation2.toInt / 16) * g2.toInt / 32768 := by
    rw [percussion_shift_fifteen, percussion_mul_exact _ _ (by rw [s2]; omega), s2]
  generalize ((filtered1 + (excitation1 >>> 4)) * g1) >>> 15 = P1 at p1
  generalize ((filtered2 + (excitation2 >>> 4)) * g2) >>> 15 = P2 at p2
  have sum : (P1 + P2 + noise).toInt = P1.toInt + P2.toInt + noise.toInt := by
    rw [percussion_add_exact, percussion_add_exact _ _ (by omega)]
    rw [percussion_add_exact _ _ (by omega)]
    omega
  rw [percussion_keep16 _ (by rw [percussion_clip_value]; omega) (by rw [percussion_clip_value]; omega),
    percussion_clip_value, sum, p1, p2]

/-- The cymbal's sample is exact: the metallic and white noises each clipped to ±32767, then the blend from
the first toward the second by `xfade` parts in 32768, which lands between them and fits 16 bits. The
product inside reaches at most 65534 times 32767 and stays inside 32 bits.
Why it matters: the cymbal's blend cannot wrap at any blend setting. -/
theorem percussion_cymbal_never_wraps (metal white xfade : Int32)
    (xfadeFits : 0 ≤ xfade.toInt ∧ xfade.toInt ≤ 32767) :
    (Percussion.cymbalOut metal white xfade).toInt =
      max (-32767) (min 32767 metal.toInt)
        + (max (-32767) (min 32767 white.toInt) - max (-32767) (min 32767 metal.toInt)) * xfade.toInt
          / 32768 := by
  unfold Percussion.cymbalOut
  have cm := percussion_clip_value metal
  have cw := percussion_clip_value white
  generalize Digital.clip metal = m at cm
  generalize Digital.clip white = w at cw
  have d : (w - m).toInt = w.toInt - m.toInt := percussion_sub_exact _ _ (by omega)
  have small := percussion_abs_mul_le (w.toInt - m.toInt) xfade.toInt 65534 32767 (by omega) (by omega)
  have p : ((w - m) * xfade).toInt = (w.toInt - m.toInt) * xfade.toInt := by
    rw [percussion_mul_exact _ _ (by rw [d]; omega), d]
  have between := percussion_between m.toInt w.toInt xfade.toInt 32768 (by decide) (by omega)
  have sum : (m + (((w - m) * xfade) >>> 15)).toInt =
      m.toInt + (w.toInt - m.toInt) * xfade.toInt / 32768 := by
    rw [percussion_add_exact _ _ (by rw [percussion_shift_fifteen, p]; omega), percussion_shift_fifteen, p]
  rw [percussion_keep16 _ (by rw [sum]; omega) (by rw [sum]; omega), sum, cm, cw]

/-- The drum's noise filter's three states stay within 16384 from one sample to the next, for noise of any
size and a cutoff from 0 to 32768.
Why it matters: the filtered noise ring-modulates the drum's partials every sample; a growing state would
wrap that product. -/
theorem percussion_drum_noise_stays_bounded (noise lp0 lp1 lp2 f : Int32)
    (lp0Fits : lp0.toInt.natAbs ≤ 16384) (lp1Fits : lp1.toInt.natAbs ≤ 16384)
    (lp2Fits : lp2.toInt.natAbs ≤ 16384) (fFits : 0 ≤ f.toInt ∧ f.toInt ≤ 32768) :
    (Percussion.drumNoise noise lp0 lp1 lp2 f).lp0.toInt.natAbs ≤ 16384 ∧
      (Percussion.drumNoise noise lp0 lp1 lp2 f).lp1.toInt.natAbs ≤ 16384 ∧
      (Percussion.drumNoise noise lp0 lp1 lp2 f).lp2.toInt.natAbs ≤ 16384 := by
  unfold Percussion.drumNoise
  dsimp only
  have nFits :
      (if noise > 16384 then (16384 : Int32) else if noise < -16384 then -16384 else noise).toInt.natAbs
        ≤ 16384 := by
    split
    · decide
    · rename_i nbig
      simp only [gt_iff_lt] at nbig; rw [Int32.lt_iff_toInt_lt] at nbig; simp at nbig
      split
      · decide
      · rename_i nsmall
        rw [Int32.lt_iff_toInt_lt] at nsmall; simp at nsmall
        omega
  generalize (if noise > 16384 then (16384 : Int32) else if noise < -16384 then -16384 else noise) = n
    at nFits
  have stage (x s : Int32) (xFits : x.toInt.natAbs ≤ 16384) (sFits : s.toInt.natAbs ≤ 16384) :
      (s + (((x - s) * f) >>> 15)).toInt.natAbs ≤ 16384 := by
    have d : (x - s).toInt = x.toInt - s.toInt := percussion_sub_exact _ _ (by omega)
    have small := percussion_abs_mul_le (x.toInt - s.toInt) f.toInt 32768 32768 (by omega) (by omega)
    have p : ((x - s) * f).toInt = (x.toInt - s.toInt) * f.toInt := by
      rw [percussion_mul_exact _ _ (by rw [d]; omega), d]
    have between := percussion_between s.toInt x.toInt f.toInt 32768 (by decide) fFits
    rw [percussion_add_exact _ _ (by rw [percussion_shift_fifteen, p]; omega), percussion_shift_fifteen, p]
    omega
  have a := stage n lp0 nFits lp0Fits
  have b := stage (lp0 + (((n - lp0) * f) >>> 15)) lp1 a lp1Fits
  have c := stage (lp1 + (((lp0 + (((n - lp0) * f) >>> 15) - lp1) * f) >>> 15)) lp2 b lp2Fits
  exact ⟨a, b, c⟩

/-- Four values well within 32 bits add without wrapping. -/
private theorem percussion_sum_four (p a b c : Int32) (pFits : p.toInt.natAbs ≤ 32768)
    (aFits : a.toInt.natAbs ≤ 98304) (bFits : b.toInt.natAbs ≤ 103104) (cFits : c.toInt.natAbs ≤ 33966) :
    (p + a + b + c).toInt = p.toInt + a.toInt + b.toInt + c.toInt := by
  have s1 : (p + a).toInt = p.toInt + a.toInt := percussion_add_exact _ _ (by omega)
  have s2 : (p + a + b).toInt = p.toInt + a.toInt + b.toInt := by
    rw [percussion_add_exact _ _ (by rw [s1]; omega), s1]
  rw [percussion_add_exact _ _ (by rw [s2]; omega), s2]

/-- The drum's sample is exact: the first partial, the second and fourth ring-modulated by the filtered noise
at the noise gain, and all partials at the harmonics gain, clipped to ±32767. Holds for a second partial
within 2048 and a fourth within 4096 (Braids starts them at 2654 and 5308 and the sine halves that), the
others within 16 bits, filtered noise within 16384, a noise gain from 0 to 12888 and a harmonics gain from
0 to 16983, the ranges Braids' drum sets (`percussion_setup_gains_in_range`).
Why it matters: the ring modulation multiplies two signals and a gain; a louder second or fourth partial
would pass 32 bits. -/
theorem percussion_drum_mix_never_wraps
    (partial0 partial1 partial3 harmonics lp2 noiseGain harmonicsGain : Int32)
    (partial0Fits : partial0.toInt.natAbs ≤ 32768) (partial1Fits : partial1.toInt.natAbs ≤ 2048)
    (partial3Fits : partial3.toInt.natAbs ≤ 4096) (harmonicsFits : harmonics.toInt.natAbs ≤ 32768)
    (lp2Fits : lp2.toInt.natAbs ≤ 16384) (noiseGainFits : 0 ≤ noiseGain.toInt ∧ noiseGain.toInt ≤ 12888)
    (harmonicsGainFits : 0 ≤ harmonicsGain.toInt ∧ harmonicsGain.toInt ≤ 16983) :
    (Percussion.drumMix partial0 partial1 partial3 harmonics lp2 noiseGain harmonicsGain).toInt =
      max (-32767) (min 32767
        (partial0.toInt + (partial1.toInt * lp2.toInt / 256) * (12288 - noiseGain.toInt) / 16384
          + (partial3.toInt * lp2.toInt / 512) * noiseGain.toInt / 16384
          + harmonics.toInt * harmonicsGain.toInt / 16384)) := by
  have shape : Percussion.drumMix partial0 partial1 partial3 harmonics lp2 noiseGain harmonicsGain =
      (Digital.clip (partial0 + ((((partial1 * lp2) >>> 8) * (12288 - noiseGain)) >>> 14)
        + ((((partial3 * lp2) >>> 9) * noiseGain) >>> 14)
        + ((harmonics * harmonicsGain) >>> 14))).toInt16 := rfl
  rw [shape]
  clear shape
  have c12288 : (12288 : Int32).toInt = 12288 := by decide
  have m1 : ((partial1 * lp2) >>> 8).toInt = partial1.toInt * lp2.toInt / 256 := by
    have := percussion_abs_mul_le partial1.toInt lp2.toInt 2048 16384 partial1Fits lp2Fits
    rw [percussion_shift_eight, percussion_mul_exact _ _ (by omega)]
  have m2 : ((partial3 * lp2) >>> 9).toInt = partial3.toInt * lp2.toInt / 512 := by
    have := percussion_abs_mul_le partial3.toInt lp2.toInt 4096 16384 partial3Fits lp2Fits
    rw [percussion_shift_nine, percussion_mul_exact _ _ (by omega)]
  have ng : ((12288 : Int32) - noiseGain).toInt = 12288 - noiseGain.toInt := by
    rw [percussion_sub_exact _ _ (by rw [c12288]; omega), c12288]
  generalize (partial1 * lp2) >>> 8 = M1 at m1
  generalize (partial3 * lp2) >>> 9 = M2 at m2
  have m1Fits : M1.toInt.natAbs ≤ 131072 := by
    have := percussion_abs_mul_le partial1.toInt lp2.toInt 2048 16384 partial1Fits lp2Fits
    omega
  have m2Fits : M2.toInt.natAbs ≤ 131072 := by
    have := percussion_abs_mul_le partial3.toInt lp2.toInt 4096 16384 partial3Fits lp2Fits
    omega
  have t1 : ((M1 * ((12288 : Int32) - noiseGain)) >>> 14).toInt =
      M1.toInt * (12288 - noiseGain.toInt) / 16384 := by
    have := percussion_abs_mul_le M1.toInt (12288 - noiseGain.toInt) 131072 12288 m1Fits (by omega)
    rw [percussion_shift_fourteen, percussion_mul_exact _ _ (by rw [ng]; omega), ng]
  have t2 : ((M2 * noiseGain) >>> 14).toInt = M2.toInt * noiseGain.toInt / 16384 := by
    have := percussion_abs_mul_le M2.toInt noiseGain.toInt 131072 12888 m2Fits (by omega)
    rw [percussion_shift_fourteen, percussion_mul_exact _ _ (by omega)]
  have t3 : ((harmonics * harmonicsGain) >>> 14).toInt = harmonics.toInt * harmonicsGain.toInt / 16384 := by
    have := percussion_abs_mul_le harmonics.toInt harmonicsGain.toInt 32768 16983 harmonicsFits (by omega)
    rw [percussion_shift_fourteen, percussion_mul_exact _ _ (by omega)]
  have b1 := percussion_abs_mul_le M1.toInt (12288 - noiseGain.toInt) 131072 12288 m1Fits (by omega)
  have b2 := percussion_abs_mul_le M2.toInt noiseGain.toInt 131072 12888 m2Fits (by omega)
  have b3 := percussion_abs_mul_le harmonics.toInt harmonicsGain.toInt 32768 16983 harmonicsFits (by omega)
  generalize (M1 * ((12288 : Int32) - noiseGain)) >>> 14 = T1 at t1
  generalize (M2 * noiseGain) >>> 14 = T2 at t2
  generalize (harmonics * harmonicsGain) >>> 14 = T3 at t3
  have T1Fits : T1.toInt.natAbs ≤ 98304 := by rw [t1]; omega
  have T2Fits : T2.toInt.natAbs ≤ 103104 := by rw [t2]; omega
  have T3Fits : T3.toInt.natAbs ≤ 33966 := by rw [t3]; omega
  clear b1 b2 b3 m1Fits m2Fits c12288 ng
  have sum := percussion_sum_four partial0 T1 T2 T3 partial0Fits T1Fits T2Fits T3Fits
  rw [percussion_keep16 _ (by rw [percussion_clip_value]; omega) (by rw [percussion_clip_value]; omega),
    percussion_clip_value, sum, t1, t2, t3, m1, m2]
