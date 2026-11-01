import Firmware.NoiseSetup
import Proofs.Tables
import Proofs.BraidsData

/-!
The noise engines' setup reads tables of C data and hands the loops the numbers their sample theorems
(`Proofs/Noise.lean`) take as hypotheses. These theorems say the reads stay inside the tables and the numbers
have the ranges the loops assume, for the parameters Braids' voice sends (0 to 32767).
-/

/-- An `Int32` shifted right seven places is its value divided by 128, rounded down. -/
private theorem noise_setup_shift_seven (s : Int32) : (s >>> 7).toInt = s.toInt / 128 := by
  show (s >>> 7).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by ten places. -/
private theorem noise_setup_shift_ten (s : Int32) : (s >>> 10).toInt = s.toInt / 1024 := by
  show (s >>> 10).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- A signed value that is not negative keeps its value as an unsigned one. -/
private theorem noise_setup_toUInt32_of_nonneg (p : Int32) (nonneg : 0 ≤ p.toInt) :
    (p.toUInt32.toNat : Int) = p.toInt := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- A `UInt32` below 2^31 keeps its value as an `Int32`. -/
private theorem noise_setup_small_toInt32 (x : UInt32) (below : x.toNat < 2 ^ 31) :
    x.toInt32.toInt = (x.toNat : Int) := by
  show x.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · simp
  · simp at below ⊢; omega

/-- The filtered noise's cutoff, damping and scale read two neighbouring entries of their 257-entry tables,
both inside, for any pitch and parameter: the top byte of the shifted value is the index.
Why it matters: the three tables are C data read without a check, and the pitch can be any 16-bit value. -/
theorem noise_setup_cutoff_in_table (pitch param0 : Int16) :
    (Analog.tableIndex (pitch.toInt32.toUInt32 <<< 17) + 1).toNat ≤ 256 ∧
      (Analog.tableIndex (param0.toInt32.toUInt32 <<< 17) + 1).toNat ≤ 256 :=
  ⟨(tables_phase_reads_inside_257 _).2, (tables_phase_reads_inside_257 _).2⟩

/-- A table blend is a 16-bit value. -/
private theorem noise_setup_lut_le (table : UInt32 → UInt16) (phase : UInt32) :
    (Digital.lutAt table phase).toNat ≤ 65535 := by
  unfold Digital.lutAt
  rw [UInt16.toNat_toUInt32]
  exact Nat.le_of_lt_succ (UInt16.toNat_lt _)

/-- `scale * 32767 / f` for `0 ≤ scale < f` is between 0 and 32767. -/
private theorem noise_setup_quotient_range (scale f : Int32) (nonneg : 0 ≤ scale.toInt)
    (small : scale.toInt ≤ 65535) (above : scale.toInt < f.toInt) :
    0 ≤ (scale * 32767 / f).toInt ∧ (scale * 32767 / f).toInt ≤ 32767 := by
  have product : (scale * 32767).toInt = scale.toInt * 32767 := by
    rw [Int32.toInt_mul]; exact Int.bmod_eq_of_le (by simp; omega) (by simp; omega)
  have fPos : 0 < f.toInt := by omega
  have lo : 0 ≤ scale.toInt * 32767 / f.toInt := Int.ediv_nonneg (by omega) (by omega)
  have hi : scale.toInt * 32767 / f.toInt ≤ 32767 :=
    Int.ediv_le_of_le_mul fPos (by omega)
  rw [Int32.toInt_div, product, Int.tdiv_eq_ediv_of_nonneg (by omega),
    Int.bmod_eq_of_le (by omega) (by omega)]
  exact ⟨lo, hi⟩

/-- The filtered noise's gain correction is between 0 and 32767, which the sample theorem
`noise_corrected_never_wraps` takes as a hypothesis.
Why it matters: the correction multiplies every sample; above 32767 the product could leave 32 bits. -/
theorem noise_setup_gain_correction_in_range (pitch param0 : Int16) :
    0 ≤ (NoiseSetup.gainCorrection pitch param0).toInt ∧
      (NoiseSetup.gainCorrection pitch param0).toInt ≤ 32767 := by
  unfold NoiseSetup.gainCorrection
  dsimp only
  split
  · rename_i above
    simp only [gt_iff_lt, Int32.lt_iff_toInt_lt] at above
    have := noise_setup_lut_le NoiseSetup.scaleTable (param0.toInt32.toUInt32 <<< 17)
    have small := noise_setup_small_toInt32
      (Digital.lutAt NoiseSetup.scaleTable (param0.toInt32.toUInt32 <<< 17)) (by omega)
    exact noise_setup_quotient_range _ _ (by omega) (by omega) above
  · decide

/-- A parameter from 0 to 32767, shifted right seven places, is at most 255 as an unsigned index. -/
private theorem noise_setup_rate_index_lt (param0 : Int16) (nonneg : 0 ≤ param0.toInt) :
    (param0.toInt32 >>> 7).toUInt32.toNat ≤ 255 := by
  have hi := Int16.toInt_le param0
  have top : Int16.maxValue.toInt = 32767 := by decide
  have shifted := noise_setup_shift_seven param0.toInt32
  rw [Int16.toInt_toInt32] at shifted
  have := noise_setup_toUInt32_of_nonneg (param0.toInt32 >>> 7) (by rw [shifted]; omega)
  omega

/-- A grain's rate reads inside the 257-entry rate table for any parameter from 0 to 32767.
Why it matters: the table is C data read without a check; the index is the parameter's top eight bits. -/
theorem noise_setup_grain_rate_in_table (param0 : Int16) (nonneg : 0 ≤ param0.toInt) :
    (param0.toInt32 >>> 7).toUInt32.toNat ≤ 256 := by
  have := noise_setup_rate_index_lt param0 nonneg
  omega

/-- A grain's rate is at most 2^18 per sample. The rate table's entries are at most 32768
(`braids_data_rate_top`, checked against `resources.cc`).
Why it matters: `noise_grain_envelope_index_in_table` needs the rate below 2^18 to keep a block's envelope
reads inside the envelope table. -/
theorem noise_setup_grain_rate_bounded (param0 : Int16) :
    (NoiseSetup.grainRate param0).toNat ≤ 2 ^ 18 := by
  unfold NoiseSetup.grainRate
  rw [UInt32.toNat_shiftLeft, UInt16.toNat_toUInt32]
  have := braids_data_rate_top (param0.toInt32 >>> 7).toUInt32
  have three : (UInt32.toNat 3 % 32) = 3 := by decide
  rw [three, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  omega

/-- After the setup, a grain's rate is at most 2^18 and its envelope will not pass 2^24 + 2^22 within the
block's 16 samples, given a block that started that way (the first block starts at 0).
Why it matters: these are the two hypotheses `noise_grain_envelope_index_in_table` takes, so with this the
grain's envelope reads stay inside their table from the first block on. A grain that has ended but does not
restart keeps its envelope, which is why the bound carries the whole block's advance. -/
theorem noise_setup_grain_reset (envelope envInc word : UInt32) (param0 : Int16)
    (settled : envelope.toNat ≤ 2 ^ 24 + 2 ^ 22) (slow : envInc.toNat ≤ 2 ^ 18) :
    (NoiseSetup.grainRateStart envelope envInc word param0).toNat ≤ 2 ^ 18 ∧
      (NoiseSetup.grainEnvelopeStart envelope envInc word).toNat
        + 16 * (NoiseSetup.grainRateStart envelope envInc word param0).toNat ≤ 2 ^ 24 + 2 ^ 22 := by
  have rate := noise_setup_grain_rate_bounded param0
  unfold NoiseSetup.grainRateStart NoiseSetup.grainEnvelopeStart
  by_cases done : NoiseSetup.grainDone envelope envInc = true
  · simp only [done, Bool.true_and, ite_true]
    split
    · simp; omega
    · simp; omega
  · have playing : envelope.toNat ≤ 2 ^ 24 := by
      unfold NoiseSetup.grainDone at done
      simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or] at done
      have := done.1
      rw [UInt32.not_lt, UInt32.le_iff_toNat_le] at this
      simpa using this
    rw [Bool.not_eq_true] at done
    simp only [done, Bool.false_and, Bool.false_eq_true, ite_false]
    omega

/-- A parameter from 0 to 32767 asks for 2 to 32 quantization steps. -/
private theorem noise_setup_steps_range (prev1 : Int16) (nonneg : 0 ≤ prev1.toInt) :
    2 ≤ (NoiseSetup.numSteps prev1).toNat ∧ (NoiseSetup.numSteps prev1).toNat ≤ 32 := by
  have hi := Int16.toInt_le prev1
  have top : Int16.maxValue.toInt = 32767 := by decide
  have shifted := noise_setup_shift_ten prev1.toInt32
  rw [Int16.toInt_toInt32] at shifted
  have one : (1 : Int32).toInt = 1 := by decide
  have sum : ((1 : Int32) + (prev1.toInt32 >>> 10)).toInt = 1 + prev1.toInt / 1024 := by
    rw [Int32.toInt_add, shifted, one]; exact Int.bmod_eq_of_le (by omega) (by omega)
  have := noise_setup_toUInt32_of_nonneg ((1 : Int32) + (prev1.toInt32 >>> 10)) (by rw [sum]; omega)
  unfold NoiseSetup.numSteps
  dsimp only
  split
  · decide
  · rename_i notOne
    rw [beq_iff_eq] at notOne
    have : ((1 : Int32) + (prev1.toInt32 >>> 10)).toUInt32.toNat ≠ 1 :=
      fun e => notOne (UInt32.toNat_inj.1 (by rw [e]; rfl))
    omega

/-- The clocked noise's quantization step is between 2048 and 32768 for any held parameter from 0 to 32767.
Why it matters: the loop reduces every random value modulo this step (`Noise.clocked`); a step of 0 would be a
division by zero in C and a silent 0 in Lean, and it cannot happen because the setup never asks for fewer
than 2 steps. -/
theorem noise_setup_clock_period_positive (prev1 : Int16) (nonneg : 0 ≤ prev1.toInt) :
    2048 ≤ (NoiseSetup.quantizerDivider prev1).toNat ∧ (NoiseSetup.quantizerDivider prev1).toNat ≤ 32768 := by
  have ⟨lo, hi⟩ := noise_setup_steps_range prev1 nonneg
  unfold NoiseSetup.quantizerDivider
  rw [UInt32.toNat_div]
  have big : (65536 : UInt32).toNat = 65536 := by decide
  rw [big]
  constructor
  · exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  · exact Nat.div_le_of_le_mul (by omega)
