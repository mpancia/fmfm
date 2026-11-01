import Firmware.FmApi

/-! The FM voice (`Firmware/Fm.lean`): the sine by polynomial is bounded, exact at the quarter points and
continuous; an operator's output and a carrier's share never wrap; the envelope only falls; the increment
stays
below Nyquist; the algorithms are well founded (a modulator is always a higher operator, so a sample computed
from operator 4 down uses fresh modulators) and every one has a carrier; every shape's settings are in the
ranges those theorems need. -/

/-- An arithmetic shift right of a 32-bit number by 16 is division by 65536, rounding down. -/
private theorem fm_shift16 (x : Int32) : (x >>> 16).toInt = x.toInt / 65536 := by
  show (x >>> 16).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by 15. -/
private theorem fm_shift15 (x : Int32) : (x >>> 15).toInt = x.toInt / 32768 := by
  show (x >>> 15).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- A product that fits in 32 bits is exact. -/
private theorem fm_mul_exact (a b : Int32) (fits : (a.toInt * b.toInt).natAbs < 2 ^ 31) :
    (a * b).toInt = a.toInt * b.toInt := by
  rw [Int32.toInt_mul]; exact Int.bmod_eq_of_le (by omega) (by omega)

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

/-- The sine is a quarter value with a sign: between -32767 and 32767, for every phase.
Why it matters: an operator can never hand its modulators or the mix more than full scale, whatever phase the
modulation pushed it to; and there is no table, so there is nothing to read past: the polynomial is checked
here for every input, not trusted. -/
theorem fm_sine_bounded (phase : UInt32) : (Fm.sineAt phase).toInt.natAbs ≤ 32767 := by
  simp only [Fm.sineAt]
  have q := fm_quarter_le (Fm.folded phase)
  have v := fm_small_toInt32 (Fm.quarter (Fm.folded phase)) (by omega)
  generalize Fm.quarter (Fm.folded phase) = y at *
  split
  · rw [Int32.toInt_neg, Int.bmod_eq_of_le (by omega) (by omega)]; omega
  · omega

/-- The sine is exact where it matters: 0 at the start, 32767 at a quarter, 0 at a half, -32767 at three
quarters, 32767 being one.
Why it matters: an operator at rest sits at zero, and a sine at its peak is exactly full scale, so the
levels and depths of the shapes mean what they say. -/
theorem fm_sine_exact_at_quarters :
    Fm.sineAt 0 = 0 ∧ Fm.sineAt 0x40000000 = 32767 ∧ Fm.sineAt 0x80000000 = 0 ∧
        Fm.sineAt 0xC0000000 = -32767 := by
  decide +kernel

/-- Checked for every position in a quarter (split in two for the kernel): the next value is within two above
or one below. -/
private theorem fm_every_quarter_step :
    ∀ hi : Fin 128, ∀ lo : Fin 256, hi.val * 256 + lo.val < 32767 →
      (Fm.quarter (hi.val * 256 + lo.val).toUInt32).toNat ≤
          (Fm.quarter ((hi.val * 256 + lo.val).toUInt32 + 1)).toNat + 1 ∧
        (Fm.quarter ((hi.val * 256 + lo.val).toUInt32 + 1)).toNat ≤
          (Fm.quarter (hi.val * 256 + lo.val).toUInt32).toNat + 2 := by
  decide +kernel

/-- The quarter sine is continuous: from one position to the next it rises by at most two and falls by at most
one (the fall is rounding; the fit itself rises throughout), for every position.
Why it matters: no step in the waveform, so no click or buzz from the polynomial itself; the sine the
operators read is smooth to within the last bit, checked at all 32767 positions. -/
theorem fm_sine_continuous (x : UInt32) (inside : x.toNat < 32767) :
    (Fm.quarter x).toNat ≤ (Fm.quarter (x + 1)).toNat + 1 ∧
      (Fm.quarter (x + 1)).toNat ≤ (Fm.quarter x).toNat + 2 := by
  have split : x.toNat / 256 * 256 + x.toNat % 256 = x.toNat := by have := Nat.div_add_mod x.toNat 256; omega
  have := fm_every_quarter_step ⟨x.toNat / 256, by omega⟩ ⟨x.toNat % 256, Nat.mod_lt _ (by decide)⟩
    (by show x.toNat / 256 * 256 + x.toNat % 256 < 32767; omega)
  rw [show (⟨x.toNat / 256, by omega⟩ : Fin 128).val * 256 + (⟨x.toNat % 256, Nat.mod_lt _
      (by decide)⟩ : Fin 256).val
    = x.toNat from split] at this
  simpa using this

/-- An operator's output is its sine through its envelope: at most 32767 in size for any envelope up to one
(2^24), and nothing wraps on the way.
Why it matters: every operator's output is a sample in range whatever its modulators did; the modulators'
pushes are modular and the output is bounded, so no setting of depths can make an operator misbehave. -/
theorem fm_operator_never_wraps (phase push envelope : UInt32) (unit : envelope.toNat ≤ 2 ^ 24) :
    (Fm.operator phase push envelope).toInt.natAbs ≤ 32767 ∧
      (Fm.operator phase push envelope).toInt = (Fm.sineAt (phase + push)).toInt *
          (envelope.toNat / 256) / 65536 := by
  unfold Fm.operator
  have s := fm_sine_bounded (phase + push)
  have e : (envelope >>> 8).toNat = envelope.toNat / 256 := by
    rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have ev := fm_small_toInt32 (envelope >>> 8) (by omega)
  have fits : ((Fm.sineAt (phase + push)).toInt * (envelope >>> 8).toInt32.toInt).natAbs < 2 ^ 31 := by
    rw [ev, Int.natAbs_mul]
    calc (Fm.sineAt (phase + push)).toInt.natAbs * ((envelope >>> 8).toNat : Int).natAbs ≤ 32767 * 65536 :=
        Nat.mul_le_mul s (by rw [Int.natAbs_natCast, e]; omega)
      _ < 2 ^ 31 := by decide
  rw [fm_shift16, fm_mul_exact _ _ fits, ev, e]
  refine ⟨?_, rfl⟩
  have lNonneg : (0 : Int) ≤ ((envelope.toNat / 256 : Nat) : Int) := by omega
  have lTop : ((envelope.toNat / 256 : Nat) : Int) ≤ 65536 := by omega
  generalize (Fm.sineAt (phase + push)).toInt = o at *
  generalize ((envelope.toNat / 256 : Nat) : Int) = l at *
  rcases Int.le_total 0 o with pos | neg
  · have upper : o * l ≤ o * 65536 := Int.mul_le_mul_of_nonneg_left lTop pos
    have d1 : 0 ≤ o * l / 65536 := Int.ediv_nonneg (Int.mul_nonneg pos lNonneg) (by decide)
    have d2 : o * l / 65536 ≤ o * 65536 / 65536 := Int.ediv_le_ediv (by decide) upper
    rw [Int.mul_ediv_cancel o (by decide)] at d2
    omega
  · have lower : o * 65536 ≤ o * l := Int.mul_le_mul_of_nonpos_left neg lTop
    have d1 : o * l / 65536 ≤ 0 := by
      have := Int.ediv_le_ediv (by decide : (0 : Int) < 65536)
        (Int.mul_nonpos_of_nonpos_of_nonneg neg lNonneg)
      simpa using this
    have d2 : o * 65536 / 65536 ≤ o * l / 65536 := Int.ediv_le_ediv (by decide) lower
    rw [Int.mul_ediv_cancel o (by decide)] at d2
    omega

/-- A carrier's share never exceeds its output: the level is at most one (32767).
Why it matters: the mix of carriers is at most the sum of their levels, so a shape with levels summing to
one cannot clip (`fm_shapes_in_range`), and `Fm.saturate` only ever acts on a louder setting. -/
theorem fm_carry_never_amplifies (out : Int32) (level : UInt32) (sample : out.toInt.natAbs ≤ 32767)
    (unit : level.toNat ≤ 32767) :
    (Fm.carry out level).toInt.natAbs ≤ out.toInt.natAbs ∧
      (Fm.carry out level).toInt = out.toInt * level.toNat / 32768 := by
  unfold Fm.carry
  have lv := fm_small_toInt32 level (by omega)
  have fits : (out.toInt * level.toInt32.toInt).natAbs < 2 ^ 31 := by
    rw [lv, Int.natAbs_mul]
    calc out.toInt.natAbs * (level.toNat : Int).natAbs ≤ 32767 * 32767 :=
        Nat.mul_le_mul sample (by rw [Int.natAbs_natCast]; exact unit)
      _ < 2 ^ 31 := by decide
  rw [fm_shift15, fm_mul_exact _ _ fits, lv]
  refine ⟨?_, rfl⟩
  have lTop : (level.toNat : Int) ≤ 32767 := by omega
  have lNonneg : (0 : Int) ≤ level.toNat := by omega
  generalize out.toInt = o at *
  generalize (level.toNat : Int) = l at *
  rcases Int.le_total 0 o with pos | neg
  · have upper : o * l ≤ o * 32768 := Int.mul_le_mul_of_nonneg_left (by omega) pos
    have nn : 0 ≤ o * l := Int.mul_nonneg pos lNonneg
    have d1 : 0 ≤ o * l / 32768 := Int.ediv_nonneg nn (by decide)
    have d2 : o * l / 32768 ≤ o * 32768 / 32768 := Int.ediv_le_ediv (by decide) upper
    rw [Int.mul_ediv_cancel o (by decide)] at d2
    omega
  · have lower : o * 32768 ≤ o * l := Int.mul_le_mul_of_nonpos_left neg (by omega)
    have np : o * l ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg neg lNonneg
    have d1 : o * l / 32768 ≤ 0 := by
      have := Int.ediv_le_ediv (by decide : (0 : Int) < 32768) np; simpa using this
    have d2 : o * 32768 / 32768 ≤ o * l / 32768 := Int.ediv_le_ediv (by decide) lower
    rw [Int.mul_ediv_cancel o (by decide)] at d2
    omega

/-- The sample out of the voice is a 16-bit value within 32767 either way, and a sum already in range passes
unchanged.
Why it matters: the hold at full scale is a saturation, never a wrap: a loud shape goes flat,
    not inside out. -/
theorem fm_saturate_in_range (x : Int32) : (Fm.saturate x).toInt.natAbs ≤ 32767 ∧
    (x.toInt.natAbs ≤ 32767 → (Fm.saturate x).toInt = x.toInt) := by
  unfold Fm.saturate
  have lo := Int32.le_toInt x
  have hi := Int32.toInt_lt x
  have t : (32767 : Int32).toInt = 32767 := by decide
  have b : (-32767 : Int32).toInt = -32767 := by decide
  have t16 : (32767 : Int16).toInt = 32767 := by decide
  have b16 : (-32767 : Int16).toInt = -32767 := by decide
  split
  · rename_i h; have := Int32.lt_iff_toInt_lt.mp h; rw [t] at this; rw [t16]; omega
  · split
    · rename_i _ h; have := Int32.lt_iff_toInt_lt.mp h; rw [b] at this; rw [b16]; omega
    · rename_i h1 h2
      have a := Int32.le_iff_toInt_le.mp (Int32.not_lt.mp h1)
      have c := Int32.le_iff_toInt_le.mp (Int32.not_lt.mp h2)
      rw [t] at a; rw [b] at c
      rw [Int32.toInt_toInt16, Int.bmod_eq_of_le (by omega) (by omega)]
      omega

/-- The envelope one block on is no higher, and no lower than 15/16 of itself, for any rate below 65536
and any envelope up to one; nothing wraps.
Why it matters: an operator's envelope only ever falls, and a block cannot take more than a sixteenth of it:
the shapes' tails are smooth and a modulator never comes back once it has gone. -/
theorem fm_envelope_only_falls (envelope rate : UInt32) (unit : envelope.toNat ≤ 2 ^ 24)
    (small : rate.toNat < 65536) :
    (Fm.envelopeStep envelope rate).toNat ≤ envelope.toNat ∧
      envelope.toNat - envelope.toNat / 16 ≤ (Fm.envelopeStep envelope rate).toNat := by
  unfold Fm.envelopeStep
  have e : (envelope >>> 8).toNat = envelope.toNat / 256 := by
    rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have prod : ((envelope >>> 8) * rate).toNat = envelope.toNat / 256 * rate.toNat := by
    rw [UInt32.toNat_mul, e, Nat.mod_eq_of_lt]
    calc envelope.toNat / 256 * rate.toNat ≤ 65536 * 65535 := Nat.mul_le_mul (by omega) (by omega)
      _ < 2 ^ 32 := by decide
  have share : (((envelope >>> 8) * rate) >>> 12).toNat = envelope.toNat / 256 * rate.toNat / 4096 := by
    rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, prod]; rfl
  have le : envelope.toNat / 256 * rate.toNat / 4096 ≤ envelope.toNat / 16 := by
    have := Nat.mul_le_mul_left (envelope.toNat / 256) (show rate.toNat ≤ 65536 by omega)
    calc envelope.toNat / 256 * rate.toNat / 4096 ≤ envelope.toNat / 256 * 65536 / 4096 :=
          Nat.div_le_div_right this
      _ = envelope.toNat / 256 * 16 := by rw [show (65536 : Nat) = 16 * 4096 by rfl, ← Nat.mul_assoc,
          Nat.mul_div_cancel _ (by decide)]
      _ ≤ envelope.toNat / 16 := by omega
  rw [UInt32.toNat_sub_of_le, share]
  · omega
  · rw [UInt32.le_iff_toNat_le, share]; omega

/-- An operator's increment is at most half a cycle a sample, whatever the pitch and ratio.
Why it matters: half a cycle a sample is the Nyquist limit; an operator asked for more is held there rather
than wrapping to a wrong low pitch. -/
theorem fm_increment_below_nyquist (voiceInc ratio : UInt32) :
    (Fm.increment voiceInc ratio).toNat ≤ 2 ^ 31 := by
  simp only [Fm.increment]
  split
  · decide
  · rename_i h
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h)
    have lit : (2147483648 : UInt64).toNat = 2147483648 := by decide
    rw [lit] at this
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
    omega

/-- In every algorithm, a modulator is a higher-numbered operator than the one it modulates, and operator 1
always carries.
Why it matters: computing a sample from operator 4 down to 1, every modulator's output is already this
sample's (no one-sample lag, no cycle except the declared feedback on 4),
    and every algorithm makes a sound. -/
theorem fm_algorithms_well_founded (alg op source : UInt32) :
    (Fm.modulates alg op source = true → op < source) ∧ Fm.carries alg 1 = true := by
  constructor
  · intro h
    unfold Fm.modulates at h
    split at h <;> first | decide | simp at h
  · unfold Fm.carries
    split
    all_goals try rfl
    exfalso
    have h8 := Nat.mod_lt alg.toNat (by decide : 0 < 8)
    simp only [← UInt32.toNat_inj] at *
    simp at *
    omega

/-- Every shape's settings are in the ranges the theorems above need: ratios at most 16 (4096 in Q8), levels
at most one (32767), rates below 65536, and the carrier levels of a shape add up to at most one.
Why it matters: with `fm_carry_never_amplifies` the eight shapes cannot clip at full envelope, and with
`fm_envelope_only_falls` their envelopes behave; the numbers in the tables are checked, not trusted. -/
theorem fm_shapes_in_range (shape : UInt32) :
    (∀ op : UInt32, (Fm.ratio shape op).toNat ≤ 4096 ∧ (Fm.level shape op).toNat ≤ 32767 ∧
      (Fm.rate shape op).toNat < 65536) ∧
    (Fm.level shape 1).toNat + (Fm.level shape 2).toNat + (Fm.level shape 3).toNat +
        (Fm.level shape 4).toNat ≤ 32767 := by
  refine ⟨fun op => ⟨?_, ?_, ?_⟩, ?_⟩
  · unfold Fm.ratio; split <;> decide
  · unfold Fm.level; split <;> decide
  · unfold Fm.rate; split <;> decide
  · unfold Fm.level
    have h8 := Nat.mod_lt shape.toNat (by decide : 0 < 8)
    have cases : shape % 8 = 0 ∨ shape % 8 = 1 ∨ shape % 8 = 2 ∨ shape % 8 = 3 ∨ shape % 8 = 4 ∨
        shape % 8 = 5 ∨
        shape % 8 = 6 ∨ shape % 8 = 7 := by
      simp only [← UInt32.toNat_inj]; simp; omega
    rcases cases with h | h | h | h | h | h | h | h <;> simp only [h] <;> decide
