import Spec.Fm

/-! Integer ratios lock an operator to the carrier exactly: its phase is an exact multiple of the carrier's
at every sample, so the two waveforms share one period for ever. -/

/-- The product of two 32-bit words as a 64-bit word, in `Nat`. -/
private theorem fm_toNat_mul64 (a b : UInt32) :
    (a.toUInt64 * b.toUInt64).toNat = a.toNat * b.toNat := by
  rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
  apply Nat.mod_eq_of_lt
  have ha := UInt32.toNat_lt a
  have hb := UInt32.toNat_lt b
  have h := Nat.mul_lt_mul_of_lt_of_lt ha hb
  have e : (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 := by decide +kernel
  exact e ▸ h

/-- A ratio below 256 in Q8 (times 256) does not wrap. -/
private theorem fm_q8_toNat (r : UInt32) (fits : r.toNat < 256) : (r * 256).toNat = r.toNat * 256 := by
  have lit : (256 : UInt32).toNat = 256 := by decide
  rw [UInt32.toNat_mul, lit]
  exact Nat.mod_eq_of_lt (by omega)

/-- For an integer ratio `r` whose product with the voice's increment is below the Nyquist cap,
`Fm.increment` returns exactly `voiceInc * r`. -/
private theorem fm_increment_exact (voiceInc r : UInt32) (small : voiceInc.toNat * r.toNat < 2 ^ 31)
    (fits : r.toNat < 256) : Fm.increment voiceInc (r * 256) = voiceInc * r := by
  simp only [Fm.increment]
  have prod : ((voiceInc.toUInt64 * (r * 256).toUInt64) >>> 8).toNat = voiceInc.toNat * r.toNat := by
    rw [UInt64.toNat_shiftRight, fm_toNat_mul64, fm_q8_toNat r fits]
    have lit : (8 : UInt64).toNat = 8 := by decide
    rw [lit, Nat.shiftRight_eq_div_pow, ← Nat.mul_assoc]
    exact Nat.mul_div_cancel _ (by decide)
  split
  · rename_i h
    have := UInt64.le_iff_toNat_le.mp h
    have lit : (2147483648 : UInt64).toNat = 2147483648 := by decide
    rw [lit, prod] at this
    omega
  · apply UInt32.toNat_inj.mp
    rw [UInt64.toNat_toUInt32, prod, UInt32.toNat_mul, Nat.mod_eq_of_lt (by omega)]

/-- `UInt32` multiplication distributes over addition. -/
private theorem fm_mul_add (a b c : UInt32) : a * (b + c) = a * b + a * c := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_mul, UInt32.toNat_mul, UInt32.toNat_add]
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_add, Nat.add_mod]

/-- With both operators starting at phase 0, an operator at integer ratio `r` (Q8 value `r * 256`) has phase
exactly `r` times the carrier's after every number of samples, modulo 2^32 as the voice counts phase.
Why it matters: a harmonic ratio is not approximately harmonic but exactly: the operator's phase is a
fixed multiple of the carrier's at every sample, so there is no drift and no beating between them, however
long the note sounds. -/
theorem fm_harmonic_ratios_lock (voiceInc r : UInt32) (small : voiceInc.toNat * r.toNat < 2 ^ 31)
    (fits : r.toNat < 256) (n : Nat) :
    Fm.phaseAfter 0 (Fm.increment voiceInc (r * 256)) n = r * Fm.phaseAfter 0 voiceInc n := by
  rw [fm_increment_exact voiceInc r small fits]
  induction n with
  | zero => simp [Fm.phaseAfter]
  | succ n ih =>
    simp only [Fm.phaseAfter]
    rw [ih, fm_mul_add, UInt32.mul_comm voiceInc r]

/-- The operator's waveform at integer ratio `r` is a function of the carrier's phase alone.
Why it matters: the sum of a carrier and an operator at an integer ratio is exactly periodic with the
carrier, so the spectrum is exactly harmonic: the overtones sit on whole multiples of the fundamental and the
ear hears one pitch, forever. -/
theorem fm_integer_ratio_periodic (voiceInc r : UInt32) (small : voiceInc.toNat * r.toNat < 2 ^ 31)
    (fits : r.toNat < 256) (n : Nat) :
    Fm.sineAt (Fm.phaseAfter 0 (Fm.increment voiceInc (r * 256)) n) =
      Fm.sineAt (r * Fm.phaseAfter 0 voiceInc n) := by
  rw [fm_harmonic_ratios_lock voiceInc r small fits n]

/-- FM ORGAN (shape 54) and FM BASS (shape 50) use integer ratios on every operator; FM BELL (shape 49) does
not.
Why it matters: the organ and bass lock to the carrier by `fm_harmonic_ratios_lock`, so their partials are
exactly harmonic and the note is one steady pitch; the bell's ratios of 3.5, 7.2 and 1.4 are chosen not to
lock, and the inharmonic, slowly beating partials that follow are what make it sound like a bell. -/
theorem fm_organ_and_bass_lock :
    (∀ op : Fin 4, (Fm.ratio 54 (op.val + 1).toUInt32) % 256 = 0) ∧
    (∀ op : Fin 4, (Fm.ratio 50 (op.val + 1).toUInt32) % 256 = 0) ∧
    ¬ (∀ op : Fin 4, (Fm.ratio 49 (op.val + 1).toUInt32) % 256 = 0) := by
  decide +kernel
