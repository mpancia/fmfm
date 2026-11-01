import Firmware.Delay

/-- `min t 100` is at most 100. -/
private theorem delay_clamped_setting (t : UInt32) : (min t 100).toNat ≤ 100 := by
  rw [UInt32.min_def]; split <;> simp_all [UInt32.le_iff_toNat_le]

/-- A number below 2^31 keeps its value when read as a signed 32-bit number. -/
private theorem delay_small_stays (x : UInt32) (h : x.toNat < 2 ^ 31) : x.toInt32.toInt = x.toNat := by
  have same : x.toNat = x.toBitVec.toNat := rfl
  have small : 2 * x.toBitVec.toNat < 2 ^ 32 := by omega
  rw [Int32.toInt, UInt32.toBitVec_toInt32, BitVec.toInt_eq_toNat_cond]
  simp only [small, ↓reduceIte, same]

/-- A setting scaled to Q15 as a plain number. -/
private theorem delay_scaled_value (k t : UInt32) (small : k.toNat ≤ 32768) :
    (k * min t 100 / 100 : UInt32).toNat = k.toNat * (min t 100).toNat / 100 := by
  have := delay_clamped_setting t
  have h1 : k.toNat * (min t 100).toNat ≤ 32768 * 100 := Nat.mul_le_mul small this
  simp only [UInt32.toNat_div, UInt32.toNat_mul, UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- For every feedback setting the gain is between 0 and 0.95 (31129 in Q15), and for every tone setting the
low-pass amount is between 0.2 and 1.0.
Why it matters: an echo is always quieter than the one before it, so echoes die away at every knob position;
the delay cannot build up into a howl. -/
theorem delay_gains_in_range (setting : UInt32) :
    0 ≤ (Delay.feedbackGain setting).toInt ∧ (Delay.feedbackGain setting).toInt ≤ 31129 ∧
      6554 ≤ (Delay.toneGain setting).toInt ∧ (Delay.toneGain setting).toInt ≤ 32768 := by
  have m := delay_clamped_setting setting
  have f := delay_scaled_value 31129 setting (by decide)
  have t := delay_scaled_value 26214 setting (by decide)
  have c1 : (31129 : UInt32).toNat = 31129 := by decide
  have c2 : (26214 : UInt32).toNat = 26214 := by decide
  rw [c1] at f; rw [c2] at t
  unfold Delay.feedbackGain Delay.toneGain
  have tv : (6554 + 26214 * min setting 100 / 100 : UInt32).toNat =
      6554 + 26214 * (min setting 100).toNat / 100 := by
    rw [UInt32.toNat_add, t]; simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [delay_small_stays _ (by rw [f]; omega), delay_small_stays _ (by rw [tv]; omega), f, tv]
  omega

/-- A signal (not the one most negative number) times a gain of at most 1.0 in size fits in 46 bits with room
for the rounding and the result fits in 32. -/
private theorem delay_product_small (s g : Int32) (nonmin : -2 ^ 31 < s.toInt)
    (unit : g.toInt.natAbs ≤ 32768) : (s.toInt * g.toInt).natAbs ≤ 2 ^ 46 - 32768 := by
  rw [Int.natAbs_mul]
  have hs : s.toInt.natAbs ≤ 2 ^ 31 - 1 := by have := Int32.toInt_lt s; omega
  exact Nat.le_trans (Nat.mul_le_mul hs unit) (by decide)

/-- An arithmetic shift right of a signed 64-bit number by 15 is division by 32768, rounding down. -/
private theorem delay_shift15 (x : Int64) : (x >>> 15).toInt = x.toInt / 32768 := by
  show (x >>> 15).toBitVec.toInt = _
  rw [Int64.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- `Reverb.mul` as a plain number (as in `Proofs/Reverb.lean`, where it is private). -/
private theorem delay_mul_value (s g : Int32) (nonmin : -2 ^ 31 < s.toInt) (unit : g.toInt.natAbs ≤ 32768) :
    (Reverb.mul s g).toInt = (s.toInt * g.toInt + 16384) / 32768 := by
  unfold Reverb.mul
  have hp := delay_product_small s g nonmin unit
  rw [Int64.toInt_toInt32, delay_shift15, Int64.toInt_add, Int64.toInt_mul, Int32.toInt_toInt64,
    Int32.toInt_toInt64]
  have c : (16384 : Int64).toInt = 16384 := by decide
  rw [c]
  generalize s.toInt * g.toInt = p at *
  have e1 : Int.bmod p (2 ^ 64) = p := Int.bmod_eq_of_le (by omega) (by omega)
  rw [e1]
  have e2 : Int.bmod (p + 16384) (2 ^ 64) = p + 16384 := Int.bmod_eq_of_le (by omega) (by omega)
  rw [e2]
  clear e1 e2
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- With nothing new on the send, what goes back into the line is at most 95% of the echo plus one count
of rounding, for every feedback setting (the one most negative number left out).
Why it matters: this is the geometric decay of the echoes. With the low-pass only ever between its state
and its input (`reverb_lowpass_stays_between`), each pass round the line loses at least a twentieth, so a
tail of echoes dies away whatever the settings. -/
theorem delay_echo_shrinks (echo feedback : Int32) (nonmin : -2 ^ 31 < echo.toInt)
    (nonneg : 0 ≤ feedback.toInt) (unit : feedback.toInt ≤ 31129) :
    (Delay.input 0 echo feedback).toInt.natAbs ≤ echo.toInt.natAbs * 19 / 20 + 1 := by
  unfold Delay.input
  have v := delay_mul_value echo feedback nonmin (by omega)
  have lt := Int32.toInt_lt (Reverb.mul echo feedback)
  have ge := Int32.le_toInt (Reverb.mul echo feedback)
  have z : (0 : Int32).toInt = 0 := by decide
  rw [v] at lt ge
  have e : Int.bmod ((echo.toInt * feedback.toInt + 16384) / 32768) (2 ^ 32) =
      (echo.toInt * feedback.toInt + 16384) / 32768 := Int.bmod_eq_of_le (by omega) (by omega)
  rw [Int32.toInt_add, z, Int.zero_add, v, e]
  rcases Int.le_total 0 echo.toInt with pos | neg
  · have lo : 0 ≤ echo.toInt * feedback.toInt := Int.mul_nonneg pos nonneg
    have hi : echo.toInt * feedback.toInt ≤ echo.toInt * 31129 := Int.mul_le_mul_of_nonneg_left unit pos
    omega
  · have hi : echo.toInt * feedback.toInt ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg neg nonneg
    have lo : echo.toInt * 31129 ≤ echo.toInt * feedback.toInt := Int.mul_le_mul_of_nonpos_left neg unit
    omega

/-- The clamp at the end of `Delay.samples` keeps its result between 1 and 32767. -/
private theorem delay_clamp_in_line (n : UInt32) :
    1 ≤ (if n > 32767 then 32767 else if n = 0 then 1 else n).toNat ∧
      (if n > 32767 then 32767 else if n = 0 then 1 else n).toNat ≤ 32767 := by
  have c : (32767 : UInt32).toNat = 32767 := by decide
  split
  · rw [c]; decide
  · split
    · decide
    · rename_i notBig notZero
      rw [GT.gt, UInt32.lt_iff_toNat_lt, c] at notBig
      have nz : n.toNat ≠ 0 := fun h => notZero (UInt32.toNat.inj (by rw [h]; rfl))
      omega

/-- The delay in samples is always between 1 and 32767, so the echo is read from inside the line, never
from the sample being written (an offset of 0) and never from a wrapped-round position.
Why it matters: a TIME or TEMPO setting can never make the line read where it writes, which would be a
feedback path with no delay at all. -/
theorem delay_samples_in_line (time bpm rate : UInt32) :
    1 ≤ (Delay.samples time bpm rate).toNat ∧ (Delay.samples time bpm rate).toNat ≤ 32767 := by
  unfold Delay.samples
  exact delay_clamp_in_line _

/-- At 44.1 kHz and any tempo from 40 to 240, the note values up to a dotted sixteenth (TIME 0 to 3) give
exactly `60 * 44100 * numerator / (bpm * denominator)` samples: the line is long enough that nothing is cut short.
(Longer notes are exact too until they would pass 32767 samples, 743 ms, where they are held: a quarter note
below 81 bpm, a dotted eighth below 61, an eighth triplet or an eighth below 41.)
Why it matters: the echo lands on the beat the setting names, at every tempo the TEMPO knob allows. -/
theorem delay_short_notes_exact (time bpm : UInt32) (short : time.toNat ≤ 3) (slow : 40 ≤ bpm.toNat)
    (fast : bpm.toNat ≤ 240) :
    (Delay.samples time bpm 44100).toNat =
      60 * 44100 * (Delay.numerator time).toNat / (bpm.toNat * (Delay.denominator time).toNat) := by
  have table : ∀ (t : Fin 4) (b : Fin 201),
      (Delay.samples t.val.toUInt32 (b.val + 40).toUInt32 44100).toNat =
        60 * 44100 * (Delay.numerator t.val.toUInt32).toNat /
          ((b.val + 40).toUInt32.toNat * (Delay.denominator t.val.toUInt32).toNat) := by
    decide +kernel
  have := table ⟨time.toNat, by omega⟩ ⟨bpm.toNat - 40, by omega⟩
  simp only [Nat.sub_add_cancel slow, UInt32.ofNat_toNat] at this
  exact this

/-- A signal for the line saturates at the 16-bit ends instead of wrapping: from 32767 up it stores 32767,
from -32768 down it stores -32768, and in between it stores the signal.
Why it matters: a send louder than full scale clips at the top of the line, as tape would, rather than
flipping sign into a click that would then echo. -/
theorem delay_store_saturates (signal : Int32) :
    (32767 ≤ signal.toInt → (Delay.store signal).toInt = 32767) ∧
    (signal.toInt ≤ -32768 → (Delay.store signal).toInt = -32768) ∧
    (-32768 ≤ signal.toInt → signal.toInt ≤ 32767 → (Delay.store signal).toInt = signal.toInt) := by
  unfold Delay.store
  have c1 : (32767 : Int32).toInt = 32767 := by decide
  have c2 : (-32768 : Int32).toInt = -32768 := by decide
  have above : (signal > 32767) ↔ 32767 < signal.toInt := by
    show (32767 < signal) ↔ _; rw [Int32.lt_iff_toInt_lt, c1]
  have below : (signal < -32768) ↔ signal.toInt < -32768 := by rw [Int32.lt_iff_toInt_lt, c2]
  by_cases h1 : signal > 32767
  · have := above.mp h1
    simp only [h1, ite_true]
    exact ⟨fun _ => by decide, fun h => by omega, fun a b => by omega⟩
  · by_cases h2 : signal < -32768
    · have := below.mp h2
      simp only [h1, h2, ite_true, ite_false]
      exact ⟨fun h => by omega, fun _ => by decide, fun a b => by omega⟩
    · have a := mt above.mpr h1
      have b := mt below.mpr h2
      simp only [h1, h2, ite_false]
      rw [Int32.toInt_toInt16]
      have same : Int.bmod signal.toInt (2 ^ 16) = signal.toInt := Int.bmod_eq_of_le (by omega) (by omega)
      rw [same]
      exact ⟨fun h => by omega, fun h => by omega, fun _ _ => rfl⟩
