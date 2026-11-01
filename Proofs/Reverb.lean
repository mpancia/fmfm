import Firmware.Mix
import Firmware.Reverb
import Spec.Reverb

/-- `min t 100` is at most 100. -/
private theorem reverb_clamped_setting (t : UInt32) : (min t 100).toNat ≤ 100 := by
  rw [UInt32.min_def]; split <;> simp_all [UInt32.le_iff_toNat_le]

/-- The loop gain as a plain number. -/
private theorem reverb_time_gain_value (t : UInt32) :
    (11469 + 20644 * min t 100 / 100 : UInt32).toNat = 11469 + 20644 * (min t 100).toNat / 100 := by
  have := reverb_clamped_setting t
  have h1 : 20644 * (min t 100).toNat < 4294967296 := by omega
  simp only [UInt32.toNat_add, UInt32.toNat_div, UInt32.toNat_mul, UInt32.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 20644 % 4294967296 * (min t 100).toNat < 4294967296)]
  simp only [Nat.reducePow, Nat.reduceMod]
  omega

/-- The low-pass amount as a plain number. -/
private theorem reverb_bright_gain_value (t : UInt32) :
    (19661 + 12124 * min t 100 / 100 : UInt32).toNat = 19661 + 12124 * (min t 100).toNat / 100 := by
  have := reverb_clamped_setting t
  have h1 : 12124 * (min t 100).toNat < 4294967296 := by omega
  simp only [UInt32.toNat_add, UInt32.toNat_div, UInt32.toNat_mul, UInt32.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 12124 % 4294967296 * (min t 100).toNat < 4294967296)]
  simp only [Nat.reducePow, Nat.reduceMod]
  omega

/-- A number below 2^31 keeps its value when read as a signed 32-bit number. -/
private theorem reverb_small_stays (x : UInt32) (h : x.toNat < 2 ^ 31) : x.toInt32.toInt = x.toNat := by
  have same : x.toNat = x.toBitVec.toNat := rfl
  have small : 2 * x.toBitVec.toNat < 2 ^ 32 := by omega
  rw [Int32.toInt, UInt32.toBitVec_toInt32, BitVec.toInt_eq_toNat_cond]
  simp only [small, ↓reduceIte, same]

/-- A sample position is always inside the shared delay memory, whatever the write position, line start and
offset.
Why it matters: a read or write can never land outside the memory, so no setting of a knob can crash the
reverb. -/
theorem reverb_position_in_ring (write base offset : UInt32) :
    (Reverb.pos write base offset).toNat < 32768 := by
  unfold Reverb.pos
  rw [UInt32.toNat_and]
  have : (32767 : UInt32).toNat = 32767 := rfl
  rw [this]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by omega)

/-- At every scale up to 400 (353 is the shipped one), each delay line ends inside the memory, and each line
starts one sample after the previous one ends.
Why it matters: the ten lines never overlap, so one line cannot overwrite another, and none runs off the
end. -/
theorem reverb_lines_fit_and_do_not_overlap (scale : UInt32) (small : scale.toNat ≤ 400) (line : UInt32)
    (exists_ : line.toNat < 10) :
    (Reverb.start scale line).toNat + (Reverb.length scale line).toNat < 32768 ∧
      (line.toNat < 9 → (Reverb.start scale (line + 1)).toNat =
        (Reverb.start scale line).toNat + (Reverb.length scale line).toNat + 1) := by
  have table : ∀ (s : Fin 401) (l : Fin 10),
      let at_ := s.val.toUInt32; let line := l.val.toUInt32
      (Reverb.start at_ line).toNat + (Reverb.length at_ line).toNat < 32768 ∧
      (l.val < 9 → (Reverb.start at_ (line + 1)).toNat =
        (Reverb.start at_ line).toNat + (Reverb.length at_ line).toNat + 1) := by
    decide +kernel
  have := table ⟨scale.toNat, by omega⟩ ⟨line.toNat, exists_⟩
  simpa using this

/-- For every decay-time setting, the loop gain is positive and below 1.0 (at most 0.98), and for every
brightness setting the low-pass amount is too (at most 0.97).
Why it matters: the tail always dies away; no knob position makes the reverb feed back on itself and grow.
This is about the gain settings, not a proof that the whole network is stable. -/
theorem reverb_gains_below_one (setting : UInt32) :
    0 < (Reverb.timeGain setting).toInt ∧ (Reverb.timeGain setting).toInt < 32768 ∧
      0 < (Reverb.brightGain setting).toInt ∧ (Reverb.brightGain setting).toInt < 32768 := by
  have m := reverb_clamped_setting setting
  have t := reverb_time_gain_value setting
  have b := reverb_bright_gain_value setting
  unfold Reverb.timeGain Reverb.brightGain
  rw [reverb_small_stays _ (by omega), reverb_small_stays _ (by omega), t, b]
  omega

/-- The signal stored in the delay memory is the signal divided by 8, rounded towards zero, and it saturates
at the ends of the 16-bit range instead of wrapping around: from 262144 up it stores 32767, from -262152
down it stores -32768, and in between it is within 7 of the signal (times 8).
Why it matters: a loud signal in the loops clips like an overdriven analogue stage; it never wraps to the
opposite sign, which is the harsh noise a digital reverb is known for. -/
theorem reverb_compress_saturates (signal : Int32) :
    (262144 ≤ signal.toInt → (Reverb.compress signal).toInt = 32767) ∧
    (signal.toInt ≤ -262152 → (Reverb.compress signal).toInt = -32768) ∧
    (-262152 < signal.toInt → signal.toInt < 262144 →
      (Reverb.compress signal).toInt * 8 ≤ signal.toInt + 7 ∧
        signal.toInt ≤ (Reverb.compress signal).toInt * 8 + 7) := by
  have tdiv : ∀ a : Int, a.tdiv 8 = if 0 ≤ a then a / 8 else -((-a) / 8) := by
    intro a
    rw [Int.tdiv_eq_ediv]
    split <;> split <;> simp [Int.sign] <;> omega
  have stored : (signal / 8).toInt = signal.toInt.tdiv 8 := by
    rw [Int32.toInt_div_of_ne_right]; · rfl
    decide
  have hd := stored
  have hlt := Int32.toInt_lt signal
  have hge := Int32.le_toInt signal
  unfold Reverb.compress
  dsimp only
  have c1 : (32767 : Int32).toInt = 32767 := by decide
  have c2 : (-32768 : Int32).toInt = -32768 := by decide
  have above : (signal / 8 > 32767) ↔ (32767 < (signal / 8).toInt) := by
    show (32767 < signal / 8) ↔ _
    rw [Int32.lt_iff_toInt_lt, c1]
  have below : (signal / 8 < -32768) ↔ ((signal / 8).toInt < -32768) := by
    rw [Int32.lt_iff_toInt_lt, c2]
  rw [tdiv] at hd
  by_cases h1 : signal / 8 > 32767
  · have := above.mp h1
    simp only [h1, ite_true]
    exact ⟨fun _ => by decide, fun h => by split at hd <;> omega, fun a b => by split at hd <;> omega⟩
  · by_cases h2 : signal / 8 < -32768
    · have := below.mp h2
      simp only [h1, h2, ite_true, ite_false]
      exact ⟨fun h => by split at hd <;> omega, fun _ => by decide, fun a b => by split at hd <;> omega⟩
    · have a := mt above.mpr h1
      have b := mt below.mpr h2
      simp only [h1, h2, ite_false]
      have within := Int32.toInt_toInt16 (signal / 8)
      rw [Int.bmod] at within
      refine ⟨fun h => by omega, fun h => by omega, fun l u => ?_⟩
      rw [within]
      have a' : (signal / 8).toInt ≤ 32767 := by omega
      have b' : -32768 ≤ (signal / 8).toInt := by omega
      split at hd <;> split <;> omega

/-- An arithmetic shift right of a signed 64-bit number by 15 is division by 32768, rounding down. -/
private theorem reverb_shift15 (x : Int64) : (x >>> 15).toInt = x.toInt / 32768 := by
  show (x >>> 15).toBitVec.toInt = _
  rw [Int64.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by 16. -/
private theorem reverb_shift16 (x : Int64) : (x >>> 16).toInt = x.toInt / 65536 := by
  show (x >>> 16).toBitVec.toInt = _
  rw [Int64.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same for a 32-bit number by 1. -/
private theorem reverb_shift1 (x : Int32) : (x >>> 1).toInt = x.toInt / 2 := by
  show (x >>> 1).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- A 32-bit subtraction whose inputs are both below a quarter of the range is exact. -/
private theorem reverb_sub_exact (a b : Int32) (ha : a.toInt.natAbs < 2 ^ 30) (hb : b.toInt.natAbs < 2 ^ 30) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int32.toInt_sub]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A 32-bit addition whose true sum fits is exact. -/
private theorem reverb_add_exact (a b : Int32) (fits : (a.toInt + b.toInt).natAbs < 2 ^ 31) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A signal (not the one most negative number) times a gain of at most 1.0 in size fits in 46 bits with room
for the rounding and the result fits in 32. -/
private theorem reverb_product_small (s g : Int32) (nonmin : -2 ^ 31 < s.toInt)
    (unit : g.toInt.natAbs ≤ 32768) :
    (s.toInt * g.toInt).natAbs ≤ 2 ^ 46 - 32768 := by
  rw [Int.natAbs_mul]
  have hs : s.toInt.natAbs ≤ 2 ^ 31 - 1 := by have := Int32.toInt_lt s; omega
  exact Nat.le_trans (Nat.mul_le_mul hs unit) (by decide)

/-- `Reverb.mul` as a plain number: the product plus a half, divided by 32768 rounding down. -/
private theorem reverb_mul_value (s g : Int32) (nonmin : -2 ^ 31 < s.toInt) (unit : g.toInt.natAbs ≤ 32768) :
    (Reverb.mul s g).toInt = (s.toInt * g.toInt + 16384) / 32768 := by
  unfold Reverb.mul
  have hp := reverb_product_small s g nonmin unit
  rw [Int64.toInt_toInt32, reverb_shift15, Int64.toInt_add, Int64.toInt_mul, Int32.toInt_toInt64,
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

/-- A signal times a gain between 0 and 1.0 keeps its sign and never grows: the result lies between zero and
the signal. (The one most negative 32-bit number is left out; no signal in the reverb comes near it.)
Why it matters: the loop gain and the low-pass amount are such gains, so each pass round a loop cannot make
a sample louder than it went in, rounding included. -/
theorem reverb_gain_never_amplifies (signal gain : Int32) (nonmin : -2 ^ 31 < signal.toInt)
    (nonneg : 0 ≤ gain.toInt) (unit : gain.toInt ≤ 32768) :
    (0 ≤ signal.toInt →
      0 ≤ (Reverb.mul signal gain).toInt ∧ (Reverb.mul signal gain).toInt ≤ signal.toInt) ∧
    (signal.toInt ≤ 0 →
      signal.toInt ≤ (Reverb.mul signal gain).toInt ∧ (Reverb.mul signal gain).toInt ≤ 0) := by
  rw [reverb_mul_value signal gain nonmin (by omega)]
  constructor
  · intro hs
    have lo : 0 ≤ signal.toInt * gain.toInt := Int.mul_nonneg hs nonneg
    have hi : signal.toInt * gain.toInt ≤ signal.toInt * 32768 := Int.mul_le_mul_of_nonneg_left unit hs
    omega
  · intro hs
    have hi : signal.toInt * gain.toInt ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hs nonneg
    have lo : signal.toInt * 32768 ≤ signal.toInt * gain.toInt := Int.mul_le_mul_of_nonpos_left hs unit
    omega

/-- One step of the low-pass lands between its old state and the new signal, for any amount from 0 to 1.0,
when both are within a quarter of the 32-bit range (the loops hold at most 8.0, which is 1/8192 of it).
Why it matters: the filter in each loop can only smooth; it cannot overshoot, ring or add level of its own. -/
theorem reverb_lowpass_stays_between (state signal amount : Int32) (hs : state.toInt.natAbs < 2 ^ 30)
    (hx : signal.toInt.natAbs < 2 ^ 30) (nonneg : 0 ≤ amount.toInt) (unit : amount.toInt ≤ 32768) :
    min state.toInt signal.toInt ≤ (Reverb.lowpass state signal amount).toInt ∧
      (Reverb.lowpass state signal amount).toInt ≤ max state.toInt signal.toInt := by
  unfold Reverb.lowpass
  have d := reverb_sub_exact signal state hx hs
  have m := reverb_gain_never_amplifies (signal - state) amount (by omega) nonneg unit
  rw [d] at m
  rw [reverb_add_exact _ _ (by omega)]
  omega

/-- A point read between two stored neighbours lies between them, for any fraction below 1.0, when both are
within a quarter of the 32-bit range.
Why it matters: a modulated delay reads between samples; the interpolation can only blend, never add a
spike. -/
theorem reverb_interpolation_stays_between (a b fraction : Int32) (ha : a.toInt.natAbs < 2 ^ 30)
    (hb : b.toInt.natAbs < 2 ^ 30) (nonneg : 0 ≤ fraction.toInt) (unit : fraction.toInt < 65536) :
    min a.toInt b.toInt ≤ (Reverb.interpolate a b fraction).toInt ∧
      (Reverb.interpolate a b fraction).toInt ≤ max a.toInt b.toInt := by
  unfold Reverb.interpolate
  have d := reverb_sub_exact b a hb ha
  have step : ((((b - a).toInt64 * fraction.toInt64) >>> 16).toInt32).toInt =
        ((b.toInt - a.toInt) * fraction.toInt) / 65536 ∧
      (0 ≤ b.toInt - a.toInt → 0 ≤ ((b.toInt - a.toInt) * fraction.toInt) / 65536 ∧
        ((b.toInt - a.toInt) * fraction.toInt) / 65536 ≤ b.toInt - a.toInt) ∧
      (b.toInt - a.toInt ≤ 0 → b.toInt - a.toInt ≤ ((b.toInt - a.toInt) * fraction.toInt) / 65536 ∧
        ((b.toInt - a.toInt) * fraction.toInt) / 65536 ≤ 0) := by
    rw [Int64.toInt_toInt32, reverb_shift16, Int64.toInt_mul, Int32.toInt_toInt64, Int32.toInt_toInt64, d]
    have pn : (b.toInt - a.toInt).natAbs < 2 ^ 31 := by omega
    generalize b.toInt - a.toInt = p at *
    have pb : p.natAbs * fraction.toInt.natAbs ≤ (2 ^ 31 - 1) * 65535 := Nat.mul_le_mul (by omega) (by omega)
    have pa : (p * fraction.toInt).natAbs ≤ (2 ^ 31 - 1) * 65535 := by rw [Int.natAbs_mul]; exact pb
    have e1 : Int.bmod (p * fraction.toInt) (2 ^ 64) = p * fraction.toInt :=
      Int.bmod_eq_of_le (by omega) (by omega)
    rw [e1]
    refine ⟨Int.bmod_eq_of_le (by omega) (by omega), ?_, ?_⟩
    · intro hp
      have l := Int.mul_nonneg hp nonneg
      have h := Int.mul_le_mul_of_nonneg_left (show fraction.toInt ≤ 65536 by omega) hp
      omega
    · intro hp
      have l := Int.mul_nonpos_of_nonpos_of_nonneg hp nonneg
      have h := Int.mul_le_mul_of_nonpos_left hp (show fraction.toInt ≤ 65536 by omega)
      omega
  obtain ⟨v, pos, neg⟩ := step
  rw [reverb_add_exact _ _ (by rw [v]; omega), v]
  omega

/-- The final clamp of the sine keeps its result within 32767 either way. -/
private theorem reverb_clamp_bounded (z : Int32) :
    (if z > 32767 then 32767 else if z < -32767 then -32767 else z).toInt.natAbs ≤ 32767 := by
  have c1 : (32767 : Int32).toInt = 32767 := by decide
  have c2 : (-32767 : Int32).toInt = -32767 := by decide
  split
  · rw [c1]; decide
  · split
    · rw [c2]; decide
    · rename_i h1 h2
      rw [GT.gt, Int32.lt_iff_toInt_lt, c1] at h1
      rw [Int32.lt_iff_toInt_lt, c2] at h2
      omega

/-- The sine is within 32767 either way. -/
private theorem reverb_sine_bounded (phase : UInt32) : (Reverb.sine phase).toInt.natAbs ≤ 32767 := by
  unfold Reverb.sine
  exact reverb_clamp_bounded _

/-- The LFO's wobble is between 0 and 32767 (0 and 1.0 in Q15) at every phase.
Why it matters: the delay modulation below relies on the wobble never going negative or past 1.0, so a
modulated delay can only be between its base time and its base plus its depth. -/
theorem reverb_lfo_in_range (phase : UInt32) :
    0 ≤ (Reverb.lfo phase).toInt ∧ (Reverb.lfo phase).toInt ≤ 32767 := by
  unfold Reverb.lfo
  have s := reverb_sine_bounded (phase + 1073741824)
  have c : (32768 : Int32).toInt = 32768 := by decide
  rw [reverb_shift1, reverb_add_exact _ _ (by rw [c]; omega), c]
  omega

/-- The modulated offset as a plain number, when nothing overflows. -/
private theorem reverb_mod_offset_value (base depth scale lfo : UInt32) (hb : base.toNat ≤ 4680)
    (hd : depth.toNat ≤ 100) (hs : scale.toNat ≤ 400) (hl : lfo.toNat ≤ 32767) :
    (Reverb.modOffset base depth scale lfo).toNat =
      base.toNat * scale.toNat * 256 + depth.toNat * scale.toNat * lfo.toNat / 128 := by
  unfold Reverb.modOffset
  have p1 : base.toNat * scale.toNat ≤ 4680 * 400 := Nat.mul_le_mul hb hs
  have p3 : depth.toNat * scale.toNat ≤ 100 * 400 := Nat.mul_le_mul hd hs
  have p2 : depth.toNat * scale.toNat * lfo.toNat ≤ 100 * 400 * 32767 := Nat.mul_le_mul p3 hl
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_shiftLeft, UInt32.toNat_shiftRight,
    UInt32.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (by omega : base.toNat * scale.toNat < 4294967296)]
  rw [Nat.mod_eq_of_lt (by omega : base.toNat * scale.toNat * 256 < 4294967296)]
  rw [Nat.mod_eq_of_lt (by omega : depth.toNat * scale.toNat < 4294967296)]
  rw [Nat.mod_eq_of_lt (by omega : depth.toNat * scale.toNat * lfo.toNat < 4294967296)]
  omega

/-- A line's length as a plain number. -/
private theorem reverb_length_value (scale line : UInt32) (hs : scale.toNat ≤ 400) :
    (Reverb.length scale line).toNat = ((Reverb.baseLength line).toNat * scale.toNat + 128) / 256 := by
  unfold Reverb.length
  have b : (Reverb.baseLength line).toNat ≤ 4782 := by
    unfold Reverb.baseLength; split <;> decide
  have p : (Reverb.baseLength line).toNat * scale.toNat ≤ 4782 * 400 := Nat.mul_le_mul b hs
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_shiftRight, UInt32.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (by omega : (Reverb.baseLength line).toNat * scale.toNat < 4294967296)]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- The two modulated reads in the glue, the first diffuser (10 samples plus up to 60, line 0 of 113) and the
long delay of the second loop (4680 plus up to 100, line 9 of 4782), read a sample and its older neighbour
that are both inside their own line, whatever the LFO does, at every scale from 192 to 400 (353 is the
shipped one; below 192 the long delay's margin of two samples at Clouds' size is lost to rounding).
Why it matters: a modulated read that ran past the end of its line would read the next line's samples, a
quiet bug the differential test could miss. With `reverb_position_in_ring` and the line layout, every read
is in the memory and in its line. -/
theorem reverb_modulated_read_stays_in_line (scale lfo : UInt32) (lo : 192 ≤ scale.toNat)
    (hi : scale.toNat ≤ 400) (wobble : lfo.toNat ≤ 32767) :
    (Reverb.modOffset 10 60 scale lfo >>> 16).toNat + 1 < (Reverb.length scale 0).toNat ∧
      (Reverb.modOffset 4680 100 scale lfo >>> 16).toNat + 1 < (Reverb.length scale 9).toNat := by
  rw [UInt32.toNat_shiftRight, UInt32.toNat_shiftRight,
    reverb_mod_offset_value _ _ _ _ (by decide) (by decide) hi wobble,
    reverb_mod_offset_value _ _ _ _ (by decide) (by decide) hi wobble,
    reverb_length_value _ _ hi, reverb_length_value _ _ hi]
  have b0 : (Reverb.baseLength 0).toNat = 113 := by decide
  have b9 : (Reverb.baseLength 9).toNat = 4782 := by decide
  have c10 : (10 : UInt32).toNat = 10 := by decide
  have c60 : (60 : UInt32).toNat = 60 := by decide
  have c4680 : (4680 : UInt32).toNat = 4680 := by decide
  have c100 : (100 : UInt32).toNat = 100 := by decide
  rw [b0, b9, c10, c60, c4680, c100]
  simp only [UInt32.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.reduceMod]
  have w1 : 60 * scale.toNat * lfo.toNat ≤ 60 * scale.toNat * 32767 := Nat.mul_le_mul_left _ wobble
  have w2 : 100 * scale.toNat * lfo.toNat ≤ 100 * scale.toNat * 32767 := Nat.mul_le_mul_left _ wobble
  omega

/-- A signal times a gain of at most 1.0 in size, either sign, is no larger in size than the signal. -/
private theorem reverb_mul_shrinks (s g : Int32) (nonmin : -2 ^ 31 < s.toInt)
    (unit : g.toInt.natAbs ≤ 32768) : (Reverb.mul s g).toInt.natAbs ≤ s.toInt.natAbs := by
  rw [reverb_mul_value s g nonmin unit]
  have hp : (s.toInt * g.toInt).natAbs ≤ s.toInt.natAbs * 32768 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul_left _ unit
  generalize s.toInt * g.toInt = p at *
  omega

/-- The product's size, in Q15, is at most the signal's size times the gain's plus half a step of rounding. -/
private theorem reverb_mul_rounds (s g : Int32) (nonmin : -2 ^ 31 < s.toInt)
    (unit : g.toInt.natAbs ≤ 32768) :
    (Reverb.mul s g).toInt.natAbs * 32768 ≤ s.toInt.natAbs * g.toInt.natAbs + 16384 := by
  rw [reverb_mul_value s g nonmin unit]
  have hp : (s.toInt * g.toInt).natAbs = s.toInt.natAbs * g.toInt.natAbs := Int.natAbs_mul _ _
  generalize s.toInt * g.toInt = p at *
  generalize s.toInt.natAbs * g.toInt.natAbs = q at *
  omega

/-- Negating a gain of at most 1.0 in size is exact. -/
private theorem reverb_neg_value (g : Int32) (unit : g.toInt.natAbs ≤ 32768) : (-g).toInt = -g.toInt := by
  rw [Int32.toInt_neg]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- Twice a signal within a quarter of the range, as `Reverb.mul` by 2.0 computes it, is exact. -/
private theorem reverb_double_value (s : Int32) (fits : s.toInt.natAbs < 2 ^ 30) :
    (Reverb.mul s 65536).toInt = 2 * s.toInt := by
  unfold Reverb.mul
  rw [Int64.toInt_toInt32, reverb_shift15, Int64.toInt_add, Int64.toInt_mul, Int32.toInt_toInt64,
    Int32.toInt_toInt64]
  have c1 : (16384 : Int64).toInt = 16384 := by decide
  have c2 : (65536 : Int32).toInt = 65536 := by decide
  rw [c1, c2]
  have e1 : Int.bmod (s.toInt * 65536) (2 ^ 64) = s.toInt * 65536 := Int.bmod_eq_of_le (by omega) (by omega)
  rw [e1]
  have e2 : Int.bmod (s.toInt * 65536 + 16384) (2 ^ 64) = s.toInt * 65536 + 16384 :=
    Int.bmod_eq_of_le (by omega) (by omega)
  rw [e2]
  have e3 : (s.toInt * 65536 + 16384) / 32768 = 2 * s.toInt := by omega
  rw [e3]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- The low-pass output is no larger in size than the larger of its state and its signal. -/
private theorem reverb_lowpass_bounded (state signal amount : Int32) (hs : state.toInt.natAbs < 2 ^ 30)
    (hx : signal.toInt.natAbs < 2 ^ 30) (nonneg : 0 ≤ amount.toInt) (unit : amount.toInt ≤ 32768) :
    (Reverb.lowpass state signal amount).toInt.natAbs ≤ max state.toInt.natAbs signal.toInt.natAbs := by
  have := reverb_lowpass_stays_between state signal amount hs hx nonneg unit
  omega

/-- An allpass adds at most twice the size of the sample it read to the size of the accumulator, with no
wrap, when the accumulator is within a quarter of the range. -/
private theorem reverb_allpass_bounded (acc oldest gain : Int32) (accFits : acc.toInt.natAbs ≤ 2 ^ 30)
    (read : Reverb.fromMemory oldest) (unit : gain.toInt.natAbs ≤ 32768) :
    (Reverb.allpass acc oldest gain).toInt.natAbs ≤ acc.toInt.natAbs + 2 * oldest.toInt.natAbs := by
  unfold Reverb.fromMemory at *
  dsimp only [Reverb.allpass]
  have negUnit : (-gain).toInt.natAbs ≤ 32768 := by rw [reverb_neg_value gain unit]; omega
  have m1 := reverb_mul_shrinks oldest (-gain) (by omega) negUnit
  generalize Reverb.mul oldest (-gain) = fromLine at *
  have s1 := reverb_add_exact acc fromLine (by omega)
  generalize acc + fromLine = summed at *
  have m2 := reverb_mul_shrinks summed gain (by omega) unit
  generalize Reverb.mul summed gain = passed at *
  have s2 := reverb_add_exact passed oldest (by omega)
  rw [s2]
  omega

/-- A stored sample, read back, is the stored 16 bits times 8, exactly. -/
private theorem reverb_decompress_value (stored : Int16) :
    (Reverb.decompress stored).toInt = stored.toInt * 8 := by
  unfold Reverb.decompress
  rw [Int32.toInt_mul, Int16.toInt_toInt32]
  have c : (8 : Int32).toInt = 8 := by decide
  rw [c]
  have lo := Int16.le_toInt stored
  have hi := Int16.toInt_lt stored
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- What the memory holds of a signal, times 8, is no larger in size than the signal: the division rounds
towards zero and the saturation only cuts. -/
private theorem reverb_compress_shrinks (signal : Int32) :
    (Reverb.compress signal).toInt.natAbs * 8 ≤ signal.toInt.natAbs := by
  have tdiv : ∀ a : Int, a.tdiv 8 = if 0 ≤ a then a / 8 else -((-a) / 8) := by
    intro a
    rw [Int.tdiv_eq_ediv]
    split <;> split <;> simp [Int.sign] <;> omega
  have stored : (signal / 8).toInt = signal.toInt.tdiv 8 := by
    rw [Int32.toInt_div_of_ne_right]; · rfl
    decide
  rw [tdiv] at stored
  unfold Reverb.compress
  dsimp only
  have c1 : (32767 : Int32).toInt = 32767 := by decide
  have c2 : (-32768 : Int32).toInt = -32768 := by decide
  have above : (signal / 8 > 32767) ↔ (32767 < (signal / 8).toInt) := by
    show (32767 < signal / 8) ↔ _
    rw [Int32.lt_iff_toInt_lt, c1]
  have below : (signal / 8 < -32768) ↔ ((signal / 8).toInt < -32768) := by
    rw [Int32.lt_iff_toInt_lt, c2]
  by_cases h1 : signal / 8 > 32767
  · have := above.mp h1
    simp only [h1, ite_true]
    have c3 : (32767 : Int16).toInt = 32767 := by decide
    rw [c3]; split at stored <;> omega
  · by_cases h2 : signal / 8 < -32768
    · have := below.mp h2
      simp only [h1, h2, ite_true, ite_false]
      have c4 : (-32768 : Int16).toInt = -32768 := by decide
      rw [c4]; split at stored <;> omega
    · have a := mt above.mpr h1
      have b := mt below.mpr h2
      simp only [h1, h2, ite_false]
      rw [Int32.toInt_toInt16, Int.bmod_eq_of_le (by omega) (by omega)]
      split at stored <;> omega

/-- A sample read back from the memory is at most 8.0 in size. -/
private theorem reverb_decompress_in_memory (stored : Int16) :
    Reverb.fromMemory (Reverb.decompress stored) := by
  unfold Reverb.fromMemory
  rw [reverb_decompress_value]
  have lo := Int16.le_toInt stored
  have hi := Int16.toInt_lt stored
  omega

/-- Half a trip round the undriven tank scales a sample's size by at most the decay gain, plus half a step of
rounding. -/
private theorem reverb_half_trip_decays (tail decay bright diffusion : Int32) (read : Reverb.fromMemory tail)
    (decayUnit : decay.toInt.natAbs ≤ 32768) (brightNonneg : 0 ≤ bright.toInt)
    (brightUnit : bright.toInt ≤ 32768) (diffusionUnit : diffusion.toInt.natAbs ≤ 32768) :
    (Reverb.decompress (Reverb.halfTrip tail decay bright diffusion)).toInt.natAbs * 32768 ≤
      tail.toInt.natAbs * decay.toInt.natAbs + 16384 := by
  unfold Reverb.fromMemory at read
  unfold Reverb.halfTrip Reverb.loop Reverb.loopSmooth
  rw [reverb_decompress_value]
  have zero : (0 : Int32).toInt = 0 := by decide
  have quiet : Reverb.fromMemory 0 := by unfold Reverb.fromMemory; rw [zero]; decide
  have negUnit : (-diffusion).toInt.natAbs ≤ 32768 := by rw [reverb_neg_value diffusion diffusionUnit]; omega
  have shrink := reverb_mul_shrinks tail decay (by omega) decayUnit
  have round := reverb_mul_rounds tail decay (by omega) decayUnit
  have fed := reverb_add_exact 0 (Reverb.mul tail decay) (by omega)
  rw [zero, Int.zero_add] at fed
  have smooth := reverb_lowpass_bounded 0 (0 + Reverb.mul tail decay) bright (by rw [zero]; decide)
    (by omega) brightNonneg brightUnit
  rw [fed, zero, Int.natAbs_zero] at smooth
  generalize Reverb.lowpass 0 (0 + Reverb.mul tail decay) bright = smoothed at *
  have first := reverb_allpass_bounded smoothed 0 diffusion (by omega) quiet diffusionUnit
  rw [zero, Int.natAbs_zero] at first
  generalize Reverb.allpass smoothed 0 diffusion = afterA at *
  have second := reverb_allpass_bounded afterA 0 (-diffusion) (by omega) quiet negUnit
  rw [zero, Int.natAbs_zero] at second
  generalize Reverb.allpass afterA 0 (-diffusion) = afterB at *
  have cut := reverb_compress_shrinks afterB
  have chain : (Reverb.compress afterB).toInt.natAbs * 8 ≤ (Reverb.mul tail decay).toInt.natAbs := by omega
  rw [Int.natAbs_mul]
  have eight : (8 : Int).natAbs = 8 := rfl
  rw [eight]
  exact Nat.le_trans (Nat.mul_le_mul_right 32768 chain) round

/-- One trip round the undriven tank (through both loops) scales a sample's size by the decay gain squared,
plus at most one unit of rounding: in Q15, the sample read from a long delay comes back to that delay as at
most `tail · decay² / 2^30 + 1`. Each loop applies the decay gain once, so a round trip applies it twice.
The loop gain is at most 0.98 (`reverb_gains_below_one`), so the squared gain is at most 0.96. This follows
one sample's direct path with the rest of the tank quiet: what the low-passes and the allpass lines hold
comes out on later samples and is bounded by the same gains on its own trips.
Why it matters: with nothing fed in, the tail gets quieter on every trip round the tank until it is within a
rounding step of silence; no decay setting can make the reverb ring on or build up. -/
theorem reverb_round_trip_decays (tail decay bright diffusion : Int32) (read : Reverb.fromMemory tail)
    (decayUnit : decay.toInt.natAbs ≤ 32768) (brightNonneg : 0 ≤ bright.toInt)
    (brightUnit : bright.toInt ≤ 32768) (diffusionUnit : diffusion.toInt.natAbs ≤ 32768) :
    (Reverb.decompress (Reverb.roundTrip tail decay bright diffusion)).toInt.natAbs * 2 ^ 30 ≤
      tail.toInt.natAbs * decay.toInt.natAbs * decay.toInt.natAbs + 2 ^ 30 := by
  unfold Reverb.roundTrip
  have negUnit : (-diffusion).toInt.natAbs ≤ 32768 := by rw [reverb_neg_value diffusion diffusionUnit]; omega
  have first := reverb_half_trip_decays tail decay bright diffusion read decayUnit brightNonneg brightUnit
    diffusionUnit
  have second := reverb_half_trip_decays _ decay bright (-diffusion)
    (reverb_decompress_in_memory (Reverb.halfTrip tail decay bright diffusion)) decayUnit brightNonneg
    brightUnit negUnit
  generalize (Reverb.decompress (Reverb.halfTrip tail decay bright diffusion)).toInt.natAbs = middle at *
  generalize (Reverb.decompress (Reverb.halfTrip (Reverb.decompress
    (Reverb.halfTrip tail decay bright diffusion)) decay bright (-diffusion))).toInt.natAbs = out at *
  generalize tail.toInt.natAbs = t at *
  generalize decay.toInt.natAbs = d at *
  calc out * 2 ^ 30 = out * 32768 * 32768 := by rw [Nat.mul_assoc]
    _ ≤ (middle * d + 16384) * 32768 := Nat.mul_le_mul_right _ second
    _ = middle * 32768 * d + 16384 * 32768 := by rw [Nat.add_mul, Nat.mul_right_comm]
    _ ≤ (t * d + 16384) * d + 16384 * 32768 := Nat.add_le_add_right (Nat.mul_le_mul_right _ first) _
    _ = t * d * d + 16384 * d + 16384 * 32768 := by rw [Nat.add_mul]
    _ ≤ t * d * d + 16384 * 32768 + 16384 * 32768 :=
      Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ decayUnit) _) _
    _ = t * d * d + 2 ^ 30 := by omega

/-- The four diffusers add at most 64.0 to the size of a send of at most 4096.0. -/
private theorem reverb_diffuse_bounded (send inputGain diffusion oldest1 oldest2 oldest3 oldest4 : Int32)
    (sendFits : send.toInt.natAbs ≤ 2 ^ 27) (inputUnit : inputGain.toInt.natAbs ≤ 32768)
    (diffusionUnit : diffusion.toInt.natAbs ≤ 32768) (read1 : Reverb.fromMemory oldest1)
    (read2 : Reverb.fromMemory oldest2) (read3 : Reverb.fromMemory oldest3)
    (read4 : Reverb.fromMemory oldest4) :
    (Reverb.diffuse send inputGain diffusion oldest1 oldest2 oldest3 oldest4).toInt.natAbs ≤
      2 ^ 27 + 2 ^ 21 := by
  unfold Reverb.fromMemory at *
  have negUnit : (-diffusion).toInt.natAbs ≤ 32768 := by rw [reverb_neg_value diffusion diffusionUnit]; omega
  dsimp only [Reverb.diffuse]
  have fed := reverb_mul_shrinks send inputGain (by omega) inputUnit
  generalize Reverb.mul send inputGain = fed0 at *
  have a1 := reverb_allpass_bounded fed0 oldest1 (-diffusion) (by omega) read1 negUnit
  generalize Reverb.allpass fed0 oldest1 (-diffusion) = after1 at *
  have a2 := reverb_allpass_bounded after1 oldest2 (-diffusion) (by omega) read2 negUnit
  generalize Reverb.allpass after1 oldest2 (-diffusion) = after2 at *
  have a3 := reverb_allpass_bounded after2 oldest3 (-diffusion) (by omega) read3 negUnit
  generalize Reverb.allpass after2 oldest3 (-diffusion) = after3 at *
  have a4 := reverb_allpass_bounded after3 oldest4 (-diffusion) (by omega) read4 negUnit
  omega

/-- A loop's low-pass output stays within 2^28 when its input is within 2^27 + 2^21 and its state within
2^28. -/
private theorem reverb_loop_smooth_bounded (input tail state decay bright : Int32)
    (inputFits : input.toInt.natAbs ≤ 2 ^ 27 + 2 ^ 21) (stateFits : state.toInt.natAbs ≤ 2 ^ 28)
    (decayUnit : decay.toInt.natAbs ≤ 32768) (brightNonneg : 0 ≤ bright.toInt)
    (brightUnit : bright.toInt ≤ 32768) (readTail : Reverb.fromMemory tail) :
    (Reverb.loopSmooth input tail state decay bright).toInt.natAbs ≤ 2 ^ 28 := by
  unfold Reverb.fromMemory at *
  dsimp only [Reverb.loopSmooth]
  have m := reverb_mul_shrinks tail decay (by omega) decayUnit
  generalize Reverb.mul tail decay = fed at *
  have sum := reverb_add_exact input fed (by omega)
  generalize input + fed = summed at *
  have lp := reverb_lowpass_bounded state summed bright (by omega) (by omega) brightNonneg brightUnit
  generalize Reverb.lowpass state summed bright = smoothed at *
  omega

/-- A loop's two allpasses add at most 32.0 to the size of its low-pass output. -/
private theorem reverb_loop_bounded (input tail state oldestA oldestB decay bright diffusion : Int32)
    (smoothFits : (Reverb.loopSmooth input tail state decay bright).toInt.natAbs ≤ 2 ^ 28)
    (diffusionUnit : diffusion.toInt.natAbs ≤ 32768) (readA : Reverb.fromMemory oldestA)
    (readB : Reverb.fromMemory oldestB) :
    (Reverb.loop input tail state oldestA oldestB decay bright diffusion).toInt.natAbs ≤ 2 ^ 28 + 2 ^ 20 := by
  unfold Reverb.fromMemory at *
  have negUnit : (-diffusion).toInt.natAbs ≤ 32768 := by rw [reverb_neg_value diffusion diffusionUnit]; omega
  dsimp only [Reverb.loop]
  generalize Reverb.loopSmooth input tail state decay bright = smoothed at *
  have b1 := reverb_allpass_bounded smoothed oldestA diffusion (by omega) readA diffusionUnit
  generalize Reverb.allpass smoothed oldestA diffusion = afterA at *
  have b2 := reverb_allpass_bounded afterA oldestB (-diffusion) (by omega) readB negUnit
  omega

/-- The wet sample a loop hands to the mixer is exactly twice the sum the loop stores (no wrap in the
doubling or in any addition before it), it is at most 16448.0 in size (2^29 + 2^21, a quarter of the 32-bit
range), the low-pass's new state stays within 8192.0 (2^28), and the mixer's return gain of up to 2.0
(`Mix.wetSample`) then scales it with no wrap either. This holds for a send of at most 4096.0 (2^27; six
voices put far less on the bus), a low-pass state of at most 8192.0 (which the third claim keeps true from
one sample to the next, starting from a cleared state), gains of at most 1.0 in size, and samples read from
the memory (at most 8.0 each, by its 16-bit format).
Why it matters: the reverb's output can never wrap round to the opposite sign on its way into the mix, which
would turn a loud tail into full-scale noise. -/
theorem reverb_wet_never_overflows (send inputGain diffusion decay bright state returnGain : Int32)
    (oldest1 oldest2 oldest3 oldest4 tail oldestA oldestB : Int32)
    (sendFits : send.toInt.natAbs ≤ 2 ^ 27) (stateFits : state.toInt.natAbs ≤ 2 ^ 28)
    (inputUnit : inputGain.toInt.natAbs ≤ 32768) (diffusionUnit : diffusion.toInt.natAbs ≤ 32768)
    (decayUnit : decay.toInt.natAbs ≤ 32768) (brightNonneg : 0 ≤ bright.toInt)
    (brightUnit : bright.toInt ≤ 32768) (returnUnit : returnGain.toInt.natAbs ≤ 65536)
    (read1 : Reverb.fromMemory oldest1) (read2 : Reverb.fromMemory oldest2)
    (read3 : Reverb.fromMemory oldest3) (read4 : Reverb.fromMemory oldest4)
    (readTail : Reverb.fromMemory tail) (readA : Reverb.fromMemory oldestA)
    (readB : Reverb.fromMemory oldestB) :
    let input := Reverb.diffuse send inputGain diffusion oldest1 oldest2 oldest3 oldest4
    let stored := Reverb.loop input tail state oldestA oldestB decay bright diffusion
    let wet := Reverb.mul stored 65536
    wet.toInt = 2 * stored.toInt ∧ wet.toInt.natAbs ≤ 2 ^ 29 + 2 ^ 21 ∧
      (Reverb.loopSmooth input tail state decay bright).toInt.natAbs ≤ 2 ^ 28 ∧
      (Mix.wetSample wet returnGain).toInt = wet.toInt * returnGain.toInt / 32768 := by
  intro input stored wet
  have inputIs : input = Reverb.diffuse send inputGain diffusion oldest1 oldest2 oldest3 oldest4 := rfl
  have storedIs : stored = Reverb.loop input tail state oldestA oldestB decay bright diffusion := rfl
  have wetIs : wet = Reverb.mul stored 65536 := rfl
  clear_value input stored wet
  subst storedIs wetIs
  have inputFits : input.toInt.natAbs ≤ 2 ^ 27 + 2 ^ 21 := by
    rw [inputIs]
    exact reverb_diffuse_bounded send inputGain diffusion oldest1 oldest2 oldest3 oldest4 sendFits inputUnit
      diffusionUnit read1 read2 read3 read4
  have smoothFits := reverb_loop_smooth_bounded input tail state decay bright inputFits stateFits decayUnit
    brightNonneg brightUnit readTail
  have storedFits := reverb_loop_bounded input tail state oldestA oldestB decay bright diffusion smoothFits
    diffusionUnit readA readB
  generalize Reverb.loopSmooth input tail state decay bright = smoothed at *
  generalize Reverb.loop input tail state oldestA oldestB decay bright diffusion = stored at *
  have doubled := reverb_double_value stored (by omega)
  refine ⟨doubled, by omega, smoothFits, ?_⟩
  generalize Reverb.mul stored 65536 = wet at *
  clear inputIs
  unfold Mix.wetSample
  rw [Int64.toInt_toInt32, reverb_shift15, Int64.toInt_mul, Int32.toInt_toInt64, Int32.toInt_toInt64]
  have product : (wet.toInt * returnGain.toInt).natAbs ≤ (2 ^ 29 + 2 ^ 21) * 65536 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by omega) returnUnit
  generalize wet.toInt * returnGain.toInt = p at *
  have inner : p.bmod (2 ^ 64) = p := Int.bmod_eq_of_le (by omega) (by omega)
  rw [inner]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A sample read back from the memory after any number of trips round an undriven tank is still a memory
sample, at most 8.0 in size.
Why it matters: however many times a tail goes round, and whatever the gains, the 16-bit memory format caps
it; it cannot grow without bound or wrap. -/
theorem reverb_tail_stays_in_memory (tail decay bright diffusion : Int32) (read : Reverb.fromMemory tail)
    (n : Nat) : Reverb.fromMemory (Reverb.trips tail decay bright diffusion n) := by
  cases n with
  | zero => exact read
  | succ n => exact reverb_decompress_in_memory _

/-- One trip's rounding, carried through the floor division: a sample within 16385 of a share stays within
16385 of the share times the decay gain squared, when the gain is at most 32767. -/
private theorem reverb_trip_step (x0 x1 share d : Nat) (step : x1 * 2 ^ 30 ≤ x0 * d * d + 2 ^ 30)
    (within : x0 ≤ share + 16385) (below : d ≤ 32767) :
    x1 ≤ share * d * d / 2 ^ 30 + 16385 := by
  have squared : d * d ≤ 32767 * 32767 := Nat.mul_le_mul below below
  have grow : x0 * (d * d) ≤ (share + 16385) * (d * d) := Nat.mul_le_mul_right _ within
  rw [Nat.add_mul] at grow
  rw [Nat.mul_assoc] at step ⊢
  generalize d * d = p at *
  generalize share * p = s at *
  generalize x0 * p = y at *
  omega

/-- The share after `n` trips, scaled once more by the squared gain, is at most the share after `n + 1`. -/
private theorem reverb_share_step (t d n : Nat) :
    t * d ^ (2 * n) / 2 ^ (30 * n) * d * d / 2 ^ 30 ≤ t * d ^ (2 * (n + 1)) / 2 ^ (30 * (n + 1)) := by
  have pw : t * d ^ (2 * (n + 1)) = t * d ^ (2 * n) * d * d := by
    rw [Nat.mul_succ, Nat.pow_add, Nat.pow_two, ← Nat.mul_assoc, ← Nat.mul_assoc]
  have pw2 : 2 ^ (30 * (n + 1)) = 2 ^ (30 * n) * 2 ^ 30 := by rw [Nat.mul_succ, Nat.pow_add]
  rw [pw, pw2, ← Nat.div_div_eq_div_mul]
  apply Nat.div_le_div_right
  generalize t * d ^ (2 * n) = a
  generalize 2 ^ (30 * n) = b
  calc a / b * d * d = d * d * (a / b) := by ac_rfl
    _ ≤ d * d * a / b := Nat.mul_div_le_mul_div_assoc _ _ _
    _ = a * d * d / b := by ac_rfl

/-- After `n` trips round an undriven tank, a sample is at most its starting size times the decay gain to
the power `2n` (in Q15, so divided by `2^30` per trip), plus 16385 (half a unit in Q15). The decay gain
must be at most 32767, strictly below 1.0, so the geometric part really shrinks. A plain geometric bound
with no constant is false: each trip rounds by up to one unit (`reverb_round_trip_decays`), and those
roundings add up over the trips to a sum that the gain keeps below 16385, like a geometric series. The
16-bit memory stores steps of 8, so in practice the tail settles to within a few steps of silence.
Why it matters: a tail started at any level dies down towards silence and cannot creep back up: no number
of trips lets the rounding pile up into audible noise or a tone that never ends. -/
theorem reverb_tail_dies_away (tail decay bright diffusion : Int32) (read : Reverb.fromMemory tail)
    (decayBelowOne : decay.toInt.natAbs ≤ 32767) (brightNonneg : 0 ≤ bright.toInt)
    (brightUnit : bright.toInt ≤ 32768) (diffusionUnit : diffusion.toInt.natAbs ≤ 32768) (n : Nat) :
    (Reverb.trips tail decay bright diffusion n).toInt.natAbs ≤
      tail.toInt.natAbs * decay.toInt.natAbs ^ (2 * n) / 2 ^ (30 * n) + 16385 := by
  induction n with
  | zero => simp [Reverb.trips]
  | succ n ih =>
    have step := reverb_round_trip_decays (Reverb.trips tail decay bright diffusion n) decay bright diffusion
      (reverb_tail_stays_in_memory tail decay bright diffusion read n) (by omega) brightNonneg brightUnit
      diffusionUnit
    rw [Reverb.trips]
    exact Nat.le_trans (reverb_trip_step _ _ _ _ step ih decayBelowOne)
      (Nat.add_le_add_right (reverb_share_step _ _ _) _)
