import Spec.Drum
import Firmware.DrumApi
import Proofs.Fm

/-! The drum voice (`Firmware/Drum.lean`): the noise register runs through all 65535 nonzero states before it
repeats and never dies; a one-pole filter's output lies between its state and its input, so a high-pass is
bounded by the two; the envelope only falls and the sweep lands on its target from above; the six squares
sum within 16 bits and every shape's chain of filters and gains, as `voices/drum_glue.c` composes it, stays
far inside 32 bits, so the saturation at the end is a hold and never a wrap; and each shape's tail is gone in
the time its rate promises, computed in the kernel. -/

/-- An arithmetic shift right of a 32-bit number by 14 is division by 16384, rounding down. -/
private theorem drum_shift14 (x : Int32) : (x >>> 14).toInt = x.toInt / 16384 := by
  show (x >>> 14).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by 13. -/
private theorem drum_shift13 (x : Int32) : (x >>> 13).toInt = x.toInt / 8192 := by
  show (x >>> 13).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- A product that fits in 32 bits is exact. -/
private theorem drum_mul_exact (a b : Int32) (fits : (a.toInt * b.toInt).natAbs < 2 ^ 31) :
    (a * b).toInt = a.toInt * b.toInt := by
  rw [Int32.toInt_mul]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A sum that fits in 32 bits is exact. -/
private theorem drum_add_exact (a b : Int32) (fits : (a.toInt + b.toInt).natAbs < 2 ^ 31) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A difference that fits in 32 bits is exact. -/
private theorem drum_sub_exact (a b : Int32) (fits : (a.toInt - b.toInt).natAbs < 2 ^ 31) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int32.toInt_sub]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A 32-bit unsigned number below 2^31 keeps its value as a signed one. -/
private theorem drum_small_toInt32 (u : UInt32) (small : u.toNat < 2 ^ 31) : u.toInt32.toInt = u.toNat := by
  show u.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · rfl
  · simp; omega

/-- A share of a signed number by a factor up to one (`m`), rounded down, lies between nothing and the
number. -/
private theorem drum_share_between (d a m : Int) (unit : 0 ≤ a ∧ a ≤ m) (pos : 0 < m) :
    (0 ≤ d → 0 ≤ d * a / m ∧ d * a / m ≤ d) ∧ (d ≤ 0 → d ≤ d * a / m ∧ d * a / m ≤ 0) := by
  constructor
  · intro nn
    have upper : d * a ≤ d * m := Int.mul_le_mul_of_nonneg_left unit.2 nn
    have d1 : 0 ≤ d * a / m := Int.ediv_nonneg (Int.mul_nonneg nn unit.1) (by omega)
    have d2 : d * a / m ≤ d * m / m := Int.ediv_le_ediv pos upper
    rw [Int.mul_ediv_cancel d (by omega)] at d2
    exact ⟨d1, d2⟩
  · intro np
    have lower : d * m ≤ d * a := Int.mul_le_mul_of_nonpos_left np unit.2
    have d1 : d * a / m ≤ 0 := by
      have := Int.ediv_le_ediv pos (Int.mul_nonpos_of_nonpos_of_nonneg np unit.1); simpa using this
    have d2 : d * m / m ≤ d * a / m := Int.ediv_le_ediv pos lower
    rw [Int.mul_ediv_cancel d (by omega)] at d2
    exact ⟨d2, d1⟩

/-- Stepping first and then `k` times is stepping `k + 1` times. -/
private theorem drum_after_succ (s : UInt32) (k : Nat) :
    Drum.lfsrAfter s (k + 1) = Drum.lfsrAfter (Drum.lfsr s) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show Drum.lfsr (Drum.lfsrAfter s (k + 1)) = Drum.lfsr (Drum.lfsrAfter (Drum.lfsr s) k)
    rw [ih]

/-- A walk that avoids the seed for `n` steps means no step from 1 to `n` lands on it. -/
private theorem drum_orbit_sound (seed s : UInt32) (n : Nat) (walk : Drum.orbitAvoids seed s n = true) :
    ∀ k, 0 < k → k ≤ n → Drum.lfsrAfter s k ≠ seed := by
  induction n generalizing s with
  | zero => intro k h1 h2; omega
  | succ n ih =>
    intro k hk hkn
    simp only [Drum.orbitAvoids, Bool.and_eq_true, bne_iff_ne, ne_eq] at walk
    obtain ⟨first, rest⟩ := walk
    cases k with
    | zero => omega
    | succ k =>
      rw [drum_after_succ]
      cases k with
      | zero => exact first
      | succ k => exact ih (Drum.lfsr s) rest (k + 1) (by omega) (by omega)

-- the kernel walks the noise register's 65535-step orbit: a recursion deeper than the default
set_option maxRecDepth 100000 in
/-- Checked in the kernel: from state 1 the register is back at 1 after 65535 steps and at none of the
65534 steps before. -/
private theorem drum_orbit_checked :
    Drum.lfsrAfter 1 65535 = 1 ∧ Drum.orbitAvoids 1 1 65534 = true := by
  constructor <;> decide +kernel

/-- The noise register from state 1 returns to 1 after exactly 65535 steps and not before: its period is
65535, every nonzero 16-bit state (the taps are a primitive polynomial, checked by walking the orbit in the
kernel).
Why it matters: the noise behind the kick's click, the snare, the clap and the toms repeats only every
1.5 s, longer than any hit. -/
theorem drum_noise_period :
    Drum.lfsrAfter 1 65535 = 1 ∧ ∀ k, 0 < k → k < 65535 → Drum.lfsrAfter 1 k ≠ 1 :=
  ⟨drum_orbit_checked.1, fun k hk hlt => drum_orbit_sound 1 1 65534 drum_orbit_checked.2 k hk (by omega)⟩

-- the kernel walks the noise register's 65535-step orbit: a recursion deeper than the default
set_option maxRecDepth 100000 in
/-- Checked for every 16-bit state (split in two for the kernel): a nonzero state steps to a nonzero 16-bit
state. -/
private theorem drum_every_state :
    ∀ hi : Fin 256, ∀ lo : Fin 256, hi.val * 256 + lo.val ≠ 0 →
      Drum.lfsr (hi.val * 256 + lo.val).toUInt32 ≠ 0 ∧
        (Drum.lfsr (hi.val * 256 + lo.val).toUInt32).toNat < 65536 := by
  decide +kernel

/-- A nonzero 16-bit noise state steps to a nonzero 16-bit state, checked for every state.
Why it matters: the glue seeds the register with 1 and never resets it; a register at zero would stay
there. -/
theorem drum_noise_never_dies (s : UInt32) (small : s.toNat < 65536) (live : s ≠ 0) :
    Drum.lfsr s ≠ 0 ∧ (Drum.lfsr s).toNat < 65536 := by
  have split : s.toNat / 256 * 256 + s.toNat % 256 = s.toNat := by
    have := Nat.div_add_mod s.toNat 256; omega
  have nz : s.toNat / 256 * 256 + s.toNat % 256 ≠ 0 := by
    rw [split]; intro h; apply live; exact UInt32.toNat_inj.mp (by rw [h]; rfl)
  have := drum_every_state ⟨s.toNat / 256, by omega⟩ ⟨s.toNat % 256, Nat.mod_lt _ (by decide)⟩ nz
  rw [show (⟨s.toNat / 256, by omega⟩ : Fin 256).val * 256 + (⟨s.toNat % 256, Nat.mod_lt _
      (by decide)⟩ : Fin 256).val = s.toNat from split] at this
  simpa using this

/-- The noise sample is within 32767 for any state.
Why it matters: the noise feeds the filters and the gains at the same scale as a sine, so the bounds below
cover it. -/
theorem drum_noise_in_range (s : UInt32) : (Drum.noise s).toInt.natAbs ≤ 32767 := by
  unfold Drum.noise
  have top : (s &&& 0xFFFE).toNat ≤ 65534 := by
    rw [UInt32.toNat_and]
    have := Nat.and_le_right (n := s.toNat) (m := (0xFFFE : UInt32).toNat)
    exact Nat.le_trans this (by decide)
  have v := drum_small_toInt32 (s &&& 0xFFFE) (by omega)
  have lit : (32767 : Int32).toInt = 32767 := by decide
  rw [drum_sub_exact _ _ (by rw [v, lit]; omega), v, lit]
  omega

/-- A one-pole step is exact, `y + (x - y) * a / 16384` rounded down, and lies between the state `y` and the
input `x`, for a coefficient from 0 to 16384 and signals within 65535; so the high-pass (input minus
low-pass) is within `|x| + |y|`, and nothing wraps.
Why it matters: the low-pass cannot overshoot and the high-pass built from it is bounded, which is what
lets six squares and a noise pass through two filters without a 32-bit wrap. -/
theorem drum_one_pole_stays_between (y x a : Int32) (unit : 0 ≤ a.toInt ∧ a.toInt ≤ 16384)
    (xs : x.toInt.natAbs ≤ 65535) (ys : y.toInt.natAbs ≤ 65535) :
    (Drum.onePole y x a).toInt = y.toInt + (x.toInt - y.toInt) * a.toInt / 16384 ∧
      (y.toInt ≤ x.toInt → y.toInt ≤ (Drum.onePole y x a).toInt ∧ (Drum.onePole y x a).toInt ≤ x.toInt) ∧
      (x.toInt ≤ y.toInt → x.toInt ≤ (Drum.onePole y x a).toInt ∧ (Drum.onePole y x a).toInt ≤ y.toInt) ∧
      (Drum.highPass (Drum.onePole y x a) x).toInt = x.toInt - (Drum.onePole y x a).toInt ∧
      (Drum.highPass (Drum.onePole y x a) x).toInt.natAbs ≤ x.toInt.natAbs + y.toInt.natAbs := by
  have diff := drum_sub_exact x y (by omega)
  have prod : ((x - y) * a).toInt = (x.toInt - y.toInt) * a.toInt := by
    rw [← diff]; apply drum_mul_exact
    rw [diff, Int.natAbs_mul]
    calc (x.toInt - y.toInt).natAbs * a.toInt.natAbs ≤ 131070 * 16384 :=
        Nat.mul_le_mul (by omega) (by omega)
      _ < 2 ^ 31 := by decide
  have share := drum_share_between (x.toInt - y.toInt) a.toInt 16384 unit (by decide)
  have exact : (Drum.onePole y x a).toInt = y.toInt + (x.toInt - y.toInt) * a.toInt / 16384 := by
    unfold Drum.onePole
    rw [drum_add_exact, drum_shift14, prod]
    rw [drum_shift14, prod]
    generalize (x.toInt - y.toInt) * a.toInt / 16384 = q at *
    rcases Int.le_total 0 (x.toInt - y.toInt) with nn | np
    · have := share.1 nn; omega
    · have := share.2 np; omega
  have between : (y.toInt ≤ x.toInt → y.toInt ≤ (Drum.onePole y x a).toInt ∧
        (Drum.onePole y x a).toInt ≤ x.toInt) ∧
      (x.toInt ≤ y.toInt → x.toInt ≤ (Drum.onePole y x a).toInt ∧ (Drum.onePole y x a).toInt ≤ y.toInt) := by
    rw [exact]
    generalize (x.toInt - y.toInt) * a.toInt / 16384 = q at *
    constructor
    · intro le; have := share.1 (by omega); omega
    · intro le; have := share.2 (by omega); omega
  have out : (Drum.onePole y x a).toInt.natAbs ≤ 65535 := by
    rcases Int.le_total y.toInt x.toInt with le | le
    · have := between.1 le; omega
    · have := between.2 le; omega
  have hp : (Drum.highPass (Drum.onePole y x a) x).toInt = x.toInt - (Drum.onePole y x a).toInt := by
    unfold Drum.highPass; exact drum_sub_exact _ _ (by omega)
  refine ⟨exact, between.1, between.2, hp, ?_⟩
  rw [hp]
  rcases Int.le_total y.toInt x.toInt with le | le
  · have := between.1 le; omega
  · have := between.2 le; omega

/-- The envelope one sample on is no higher, and no lower than 15/16 of itself less one count, for any rate
below 65536 and envelope up to one; rate 0 holds exactly; nothing wraps.
Why it matters: a drum's envelope only falls, by at most a sixteenth a sample, and rate 0 is a hold. -/
theorem drum_envelope_only_falls (env rate : UInt32) (unit : env.toNat ≤ 2 ^ 24)
    (small : rate.toNat < 65536) :
    (Drum.envelope env rate).toNat ≤ env.toNat ∧
      env.toNat - env.toNat / 16 - 1 ≤ (Drum.envelope env rate).toNat ∧
      (rate = 0 → Drum.envelope env rate = env) := by
  have top : (env >>> 8).toNat = env.toNat / 256 := by
    rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have prodLe : env.toNat / 256 * rate.toNat ≤ 65535 * (env.toNat / 256) := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
  have prod : ((env >>> 8) * rate).toNat = env.toNat / 256 * rate.toNat := by
    rw [UInt32.toNat_mul, top, Nat.mod_eq_of_lt]; omega
  have plus : ((env >>> 8) * rate + 4095).toNat = env.toNat / 256 * rate.toNat + 4095 := by
    have lit : (4095 : UInt32).toNat = 4095 := by decide
    rw [UInt32.toNat_add, prod, lit]; exact Nat.mod_eq_of_lt (by omega)
  have share : (((env >>> 8) * rate + 4095) >>> 12).toNat = (env.toNat / 256 * rate.toNat + 4095) / 4096 := by
    rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, plus]; rfl
  have le : (env.toNat / 256 * rate.toNat + 4095) / 4096 ≤ env.toNat := by omega
  refine ⟨?_, ?_, ?_⟩
  · unfold Drum.envelope
    rw [UInt32.toNat_sub_of_le, share]
    · omega
    · rw [UInt32.le_iff_toNat_le, share]; exact le
  · unfold Drum.envelope
    rw [UInt32.toNat_sub_of_le, share]
    · omega
    · rw [UInt32.le_iff_toNat_le, share]; exact le
  · intro zero
    unfold Drum.envelope
    rw [zero, UInt32.mul_zero, UInt32.zero_add, show ((4095 : UInt32) >>> 12) = 0 from by decide,
      UInt32.sub_zero]

/-- The swept increment never rises and never goes below its target: from above it falls by `rate / 2^20`
of the distance a sample, at or below it stays on the target; for any increment below half a cycle a
sample and any rate below 8192, nothing wraps.
Why it matters: the kick's and toms' pitch sweeps land on the note with no undershoot, from a start up to
five times above it. -/
theorem drum_sweep_lands (inc target rate : UInt32) (nyquist : inc.toNat < 2 ^ 31)
    (small : rate.toNat < 8192) :
    (target ≤ inc → target ≤ Drum.sweep inc target rate ∧ Drum.sweep inc target rate ≤ inc) ∧
      (inc ≤ target → Drum.sweep inc target rate = target) := by
  unfold Drum.sweep
  split
  · rename_i le
    refine ⟨fun ge => ⟨UInt32.le_refl _, ge⟩, fun _ => rfl⟩
  · rename_i nle
    have lt := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp nle)
    refine ⟨fun _ => ?_, fun le => absurd le nle⟩
    have d : (inc - target).toNat = inc.toNat - target.toNat := UInt32.toNat_sub_of_le _ _ (by
      rw [UInt32.le_iff_toNat_le]; omega)
    have quot : ((inc - target) >>> 12).toNat = (inc.toNat - target.toNat) / 4096 := by
      rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, d]; rfl
    have prodLe : (inc.toNat - target.toNat) / 4096 * rate.toNat ≤
        8191 * ((inc.toNat - target.toNat) / 4096) := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
    have prod : (((inc - target) >>> 12) * rate).toNat = (inc.toNat - target.toNat) / 4096 * rate.toNat := by
      rw [UInt32.toNat_mul, quot, Nat.mod_eq_of_lt]; omega
    have share : ((((inc - target) >>> 12) * rate) >>> 8).toNat =
        (inc.toNat - target.toNat) / 4096 * rate.toNat / 256 := by
      rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, prod]; rfl
    have le : (inc.toNat - target.toNat) / 4096 * rate.toNat / 256 ≤ inc.toNat - target.toNat := by omega
    constructor
    · rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le, share]
      · omega
      · rw [UInt32.le_iff_toNat_le, share]; omega
    · rw [UInt32.le_iff_toNat_le, UInt32.toNat_sub_of_le, share]
      · omega
      · rw [UInt32.le_iff_toNat_le, share]; omega

/-- A sweep's start is below half a cycle a sample for any tuning and colour.
Why it matters: `drum_sweep_lands` needs the swept increment below Nyquist, and the start is its highest
value; a note above the 1.4 kHz hold starts on its tuning. -/
theorem drum_sweep_start_below_nyquist (target colour : UInt32) :
    (Drum.sweepStart target colour).toNat < 2 ^ 31 := by
  unfold Drum.sweepStart
  have t : (min target 0x08000000).toNat ≤ 2 ^ 27 := by
    rw [UInt32.min_def]; split
    · rename_i h; exact Nat.le_trans (UInt32.le_iff_toNat_le.mp h) (by decide)
    · decide
  have top : ((min target 0x08000000) >>> 13).toNat = (min target 0x08000000).toNat / 8192 := by
    rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have c : (colour % 32768).toNat ≤ 32767 := by
    have lit : (32768 : UInt32).toNat = 32768 := by decide
    rw [UInt32.toNat_mod, lit]; have := Nat.mod_lt colour.toNat (by decide : 0 < 32768); omega
  have prodLe : (min target 0x08000000).toNat / 8192 * (colour % 32768).toNat ≤
      32767 * ((min target 0x08000000).toNat / 8192) := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ c
  have prod : (((min target 0x08000000) >>> 13) * (colour % 32768)).toNat =
      (min target 0x08000000).toNat / 8192 * (colour % 32768).toNat := by
    rw [UInt32.toNat_mul, top, Nat.mod_eq_of_lt]; omega
  rw [UInt32.toNat_add, prod, Nat.mod_eq_of_lt] <;> omega

/-- Six squares of ±5461 sum within 32766 for any six phases.
Why it matters: the hi-hats and the cymbal enter their filters in the same range as a sine or the noise,
so the same filter and gain bounds cover them. -/
theorem drum_metal_sum_fits (p1 p2 p3 p4 p5 p6 : UInt32) :
    (Drum.metal p1 p2 p3 p4 p5 p6).toInt.natAbs ≤ 32766 := by
  simp only [Drum.metal, Drum.square]
  split <;> split <;> split <;> split <;> split <;> split <;> decide

/-- A square is ±5461.
Why it matters: the cowbell's two squares sum within 10922, inside the bound the band filter needs. -/
theorem drum_square_in_range (phase : UInt32) : (Drum.square phase).toInt.natAbs ≤ 5461 := by
  unfold Drum.square; split <;> decide

/-- A gain is at most its level, for any envelope up to one and level up to 32767.
Why it matters: a shape's loudest moment is its level table, which `drum_output_never_wraps` relies on. -/
theorem drum_gain_never_amplifies (env level : UInt32) (unit : env.toNat ≤ 2 ^ 24)
    (lv : level.toNat ≤ 32767) : (Drum.gain env level).toNat ≤ level.toNat := by
  unfold Drum.gain
  have top : (env >>> 9).toNat = env.toNat / 512 := by
    rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  have prodLe : env.toNat / 512 * level.toNat ≤ 32768 * level.toNat :=
    Nat.mul_le_mul_right _ (by omega)
  have prod : ((env >>> 9) * level).toNat = env.toNat / 512 * level.toNat := by
    rw [UInt32.toNat_mul, top, Nat.mod_eq_of_lt]; omega
  rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, prod]
  show env.toNat / 512 * level.toNat / 32768 ≤ level.toNat
  omega

/-- A signal within 65535 through a gain up to 32767 (four times) is exact, `x * gain / 8192` rounded down,
and within four times the signal; nothing wraps. -/
private theorem drum_scale_exact (x : Int32) (gain : UInt32) (xs : x.toInt.natAbs ≤ 65535)
    (g : gain.toNat ≤ 32767) :
    (Drum.scale x gain).toInt = x.toInt * gain.toNat / 8192 ∧
      (Drum.scale x gain).toInt.natAbs ≤ 4 * x.toInt.natAbs := by
  unfold Drum.scale
  have gv := drum_small_toInt32 gain (by omega)
  have prod : (x * gain.toInt32).toInt = x.toInt * gain.toNat := by
    rw [← gv]; apply drum_mul_exact
    rw [gv, Int.natAbs_mul]
    calc x.toInt.natAbs * (gain.toNat : Int).natAbs ≤ 65535 * 32767 :=
        Nat.mul_le_mul xs (by rw [Int.natAbs_natCast]; exact g)
      _ < 2 ^ 31 := by decide
  rw [drum_shift13, prod]
  refine ⟨rfl, ?_⟩
  have share := drum_share_between (4 * x.toInt) (gain.toNat : Int) 32768 ⟨by omega, by omega⟩ (by decide)
  have four : x.toInt * (gain.toNat : Int) / 8192 = 4 * x.toInt * (gain.toNat : Int) / 32768 := by
    rw [show (32768 : Int) = 4 * 8192 from rfl, Int.mul_assoc, Int.mul_ediv_mul_of_pos _ _ (by decide)]
  rw [four]
  rcases Int.le_total 0 x.toInt with nn | np
  · have := share.1 (by omega); omega
  · have := share.2 (by omega); omega

/-- The bound of a scaled signal: within 262140 for a signal within 65535 and a gain up to 32767. -/
private theorem drum_scale_bounded (x : Int32) (gain : UInt32) (xs : x.toInt.natAbs ≤ 65535)
    (g : gain.toNat ≤ 32767) : (Drum.scale x gain).toInt.natAbs ≤ 262140 := by
  have := (drum_scale_exact x gain xs g).2; omega

/-- Two scaled signals add exactly, within 524280. -/
private theorem drum_mix_fits (a b : Int32) (ha : a.toInt.natAbs ≤ 262140) (hb : b.toInt.natAbs ≤ 262140) :
    (a + b).toInt = a.toInt + b.toInt ∧ (a + b).toInt.natAbs ≤ 524280 := by
  have e := drum_add_exact a b (by omega)
  exact ⟨e, by rw [e]; omega⟩

/-- A band's two filter states, one sample on. -/
private theorem drum_band_states (input lp1 lp2 aH aL : Int32) (xs : input.toInt.natAbs ≤ 32767)
    (l1 : lp1.toInt.natAbs ≤ 32767) (l2 : lp2.toInt.natAbs ≤ 65535)
    (h : 0 ≤ aH.toInt ∧ aH.toInt ≤ 16384) (l : 0 ≤ aL.toInt ∧ aL.toInt ≤ 16384) :
    (Drum.onePole lp1 input aH).toInt.natAbs ≤ 32767 ∧
      (Drum.highPass (Drum.onePole lp1 input aH) input).toInt.natAbs ≤ 65534 ∧
      (Drum.onePole lp2 (Drum.highPass (Drum.onePole lp1 input aH) input) aL).toInt.natAbs ≤ 65535 := by
  have first := drum_one_pole_stays_between lp1 input aH h (by omega) (by omega)
  have s1 : (Drum.onePole lp1 input aH).toInt.natAbs ≤ 32767 := by
    rcases Int.le_total lp1.toInt input.toInt with le | le
    · have := first.2.1 le; omega
    · have := first.2.2.1 le; omega
  have hp : (Drum.highPass (Drum.onePole lp1 input aH) input).toInt.natAbs ≤ 65534 := by
    have := first.2.2.2.2; omega
  have second := drum_one_pole_stays_between lp2 (Drum.highPass (Drum.onePole lp1 input aH) input) aL l
    (by omega) l2
  refine ⟨s1, hp, ?_⟩
  rcases Int.le_total lp2.toInt (Drum.highPass (Drum.onePole lp1 input aH) input).toInt with le | le
  · have := second.2.1 le; omega
  · have := second.2.2.1 le; omega

/-- Six squares through the band filter and the gain: the sum is within 32766 (`drum_metal_sum_fits`), the
first low-pass state within 32767, the high-pass within 65534, the second low-pass within 65535 and the
gained output within 262140, for filter coefficients from 0 to 16384 (Q14) and a gain up to 32767 (Q13);
no stage wraps and the states handed on satisfy the same bounds.
Why it matters: the hi-hats and the cymbal are the most arithmetic of any shape, and no colour setting can
overflow their filters. -/
theorem drum_metal_chain_bounded (p1 p2 p3 p4 p5 p6 : UInt32) (lp1 lp2 aH aL : Int32) (gain : UInt32)
    (l1 : lp1.toInt.natAbs ≤ 32767) (l2 : lp2.toInt.natAbs ≤ 65535)
    (h : 0 ≤ aH.toInt ∧ aH.toInt ≤ 16384) (l : 0 ≤ aL.toInt ∧ aL.toInt ≤ 16384) (g : gain.toNat ≤ 32767) :
    (Drum.metal p1 p2 p3 p4 p5 p6).toInt.natAbs ≤ 32766 ∧
      (Drum.onePole lp1 (Drum.metal p1 p2 p3 p4 p5 p6) aH).toInt.natAbs ≤ 32767 ∧
      (Drum.onePole lp2 (Drum.highPass (Drum.onePole lp1 (Drum.metal p1 p2 p3 p4 p5 p6) aH)
        (Drum.metal p1 p2 p3 p4 p5 p6)) aL).toInt.natAbs ≤ 65535 ∧
      (Drum.bandOut (Drum.metal p1 p2 p3 p4 p5 p6) lp1 lp2 aH aL gain).toInt.natAbs ≤ 262140 := by
  have fits := drum_metal_sum_fits p1 p2 p3 p4 p5 p6
  have states := drum_band_states (Drum.metal p1 p2 p3 p4 p5 p6) lp1 lp2 aH aL (by omega) l1 l2 h l
  exact ⟨fits, states.1, states.2.2, drum_scale_bounded _ _ states.2.2 g⟩

/-- Every shape's mix, as `voices/drum_glue.c` composes it, is exact and within 524280 (under 2^19), for
filter states within their bounds (first stage within 32767, second within 65535), coefficients from 0 to
16384 and gains up to 32767: the kick and toms (`Drum.tunedOut`), the snare (`Drum.snareOut`), the clap
(`Drum.clapOut`), the hi-hats and cowbell (`Drum.bandOut`, with `drum_metal_chain_bounded` and
`drum_square_in_range`) and the cymbal (`Drum.cymbalOut`); the sample out is the mix clipped to 16 bits,
unchanged when already within 32767.
Why it matters: no drum's arithmetic wraps at any knob, note or phase; an overloaded shape clips. -/
theorem drum_output_never_wraps (phase p2 p3 p4 p5 p6 noise : UInt32) (lp1 lp2 lp3 lp4 aH aL uH uL : Int32)
    (gA gB : UInt32) (l1 : lp1.toInt.natAbs ≤ 32767) (l2 : lp2.toInt.natAbs ≤ 65535)
    (l3 : lp3.toInt.natAbs ≤ 32767) (l4 : lp4.toInt.natAbs ≤ 65535)
    (h : 0 ≤ aH.toInt ∧ aH.toInt ≤ 16384) (l : 0 ≤ aL.toInt ∧ aL.toInt ≤ 16384)
    (uh : 0 ≤ uH.toInt ∧ uH.toInt ≤ 16384) (ul : 0 ≤ uL.toInt ∧ uL.toInt ≤ 16384)
    (ga : gA.toNat ≤ 32767) (gb : gB.toNat ≤ 32767) :
    (Drum.tunedOut phase noise lp1 aL gA gB).toInt.natAbs ≤ 524280 ∧
      (Drum.snareOut phase p2 noise lp1 aH gA gB).toInt.natAbs ≤ 524280 ∧
      (Drum.clapOut noise lp1 lp2 aH aL gA gB).toInt.natAbs ≤ 524280 ∧
      (Drum.bandOut (Drum.metal phase p2 p3 p4 p5 p6) lp1 lp2 aH aL gA).toInt.natAbs ≤ 262140 ∧
      (Drum.bandOut (Drum.square phase + Drum.square p2) lp1 lp2 aH aL gA).toInt.natAbs ≤ 262140 ∧
      (Drum.cymbalOut phase p2 p3 p4 p5 p6 lp1 lp2 lp3 lp4 aH aL uH uL gA gB).toInt.natAbs ≤ 524280 ∧
      (∀ mix : Int32, (Drum.saturate mix).toInt.natAbs ≤ 32767 ∧
        (mix.toInt.natAbs ≤ 32767 → (Drum.saturate mix).toInt = mix.toInt)) := by
  have nz := drum_noise_in_range noise
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun mix => fm_saturate_in_range mix⟩
  · unfold Drum.tunedOut
    have sine := fm_sine_bounded phase
    have a := drum_scale_bounded (Fm.sineAt phase) gA (by omega) ga
    have filt := drum_one_pole_stays_between lp1 (Drum.noise noise) aL l (by omega) (by omega)
    have inside : (Drum.onePole lp1 (Drum.noise noise) aL).toInt.natAbs ≤ 65535 := by
      rcases Int.le_total lp1.toInt (Drum.noise noise).toInt with le | le
      · have := filt.2.1 le; omega
      · have := filt.2.2.1 le; omega
    have b := drum_scale_bounded _ gB inside gb
    exact (drum_mix_fits _ _ a b).2
  · unfold Drum.snareOut
    have s1 := fm_sine_bounded phase
    have s2 := fm_sine_bounded p2
    have pair := drum_add_exact (Fm.sineAt phase) (Fm.sineAt p2) (by omega)
    have a := drum_scale_bounded (Fm.sineAt phase + Fm.sineAt p2) gA (by rw [pair]; omega) ga
    have filt := drum_one_pole_stays_between lp1 (Drum.noise noise) aH h (by omega) (by omega)
    have b := drum_scale_bounded (Drum.highPass (Drum.onePole lp1 (Drum.noise noise) aH) (Drum.noise noise))
      gB (by have := filt.2.2.2.2; omega) gb
    exact (drum_mix_fits _ _ a b).2
  · unfold Drum.clapOut
    have states := drum_band_states (Drum.noise noise) lp1 lp2 aH aL (by omega) l1 l2 h l
    have a := drum_scale_bounded _ gA states.2.2 ga
    have b := drum_scale_bounded _ gB states.2.2 gb
    exact (drum_mix_fits _ _ a b).2
  · exact (drum_metal_chain_bounded phase p2 p3 p4 p5 p6 lp1 lp2 aH aL gA l1 l2 h l ga).2.2.2
  · have q1 := drum_square_in_range phase
    have q2 := drum_square_in_range p2
    have pair := drum_add_exact (Drum.square phase) (Drum.square p2) (by omega)
    have states := drum_band_states (Drum.square phase + Drum.square p2) lp1 lp2 aH aL
      (by rw [pair]; omega) l1 l2 h l
    exact drum_scale_bounded _ gA states.2.2 ga
  · unfold Drum.cymbalOut
    have a := (drum_metal_chain_bounded phase p2 p3 p4 p5 p6 lp1 lp2 aH aL gA l1 l2 h l ga).2.2.2
    have b := (drum_metal_chain_bounded phase p2 p3 p4 p5 p6 lp3 lp4 uH uL gB l3 l4 uh ul gb).2.2.2
    exact (drum_mix_fits _ _ a b).2

/-- Every shape's tables are in the ranges the theorems above need: rates below 65536 at every timbre
(`drum_envelope_only_falls`), sweep rates below 8192 (`drum_sweep_lands`), levels up to 32767
(`drum_gain_never_amplifies`) and filter coefficients up to 16384 (`drum_one_pole_stays_between`) at every
colour.
Why it matters: the table values are checked against the bounds, so a knob at either end still meets
every hypothesis. -/
theorem drum_shapes_in_range (shape timbre colour : UInt32) :
    (Drum.decay (Drum.rate shape) timbre).toNat < 65536 ∧
      (Drum.decay (Drum.secondRate shape) timbre).toNat < 65536 ∧
      (Drum.sweepRate shape).toNat < 8192 ∧
      (Drum.level shape colour).toNat ≤ 32767 ∧ (Drum.secondLevel shape colour).toNat ≤ 32767 ∧
      (Drum.highCoefficient shape colour).toNat ≤ 16384 ∧ (Drum.lowCoefficient shape).toNat ≤ 16384 ∧
      (Drum.upperCoefficient 0).toNat ≤ 16384 ∧ (Drum.upperCoefficient 1).toNat ≤ 16384 := by
  have decayLt : ∀ r : UInt32, (Drum.decay r timbre).toNat < 65536 := by
    intro r; unfold Drum.decay
    rw [UInt32.min_def]; split
    · rename_i h; exact Nat.lt_of_le_of_lt (UInt32.le_iff_toNat_le.mp h) (by decide)
    · decide
  have c : (colour % 32768).toNat ≤ 32767 := by
    have lit : (32768 : UInt32).toNat = 32768 := by decide
    rw [UInt32.toNat_mod, lit]; have := Nat.mod_lt colour.toNat (by decide : 0 < 32768); omega
  have l3072 : (3072 : UInt32).toNat = 3072 := by decide
  have l1024 : (1024 : UInt32).toNat = 1024 := by decide
  have band : (Drum.band colour).toNat ≤ 11263 := by
    unfold Drum.band
    have q : ((colour % 32768) >>> 2).toNat = (colour % 32768).toNat / 4 := by
      rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
    rw [UInt32.toNat_add, q, l3072, Nat.mod_eq_of_lt] <;> omega
  refine ⟨decayLt _, decayLt _, ?_, ?_, ?_, ?_, ?_, by decide, by decide⟩
  · unfold Drum.sweepRate; split <;> decide
  · unfold Drum.level; split
    all_goals try decide
    have q : ((colour % 32768) >>> 4).toNat = (colour % 32768).toNat / 16 := by
      rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
    rw [UInt32.toNat_sub_of_le, q, l3072]
    · omega
    · rw [UInt32.le_iff_toNat_le, q, l3072]; omega
  · unfold Drum.secondLevel; split
    all_goals try decide
    have q : ((colour % 32768) >>> 3).toNat = (colour % 32768).toNat / 8 := by
      rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
    rw [UInt32.toNat_add, q, l1024, Nat.mod_eq_of_lt] <;> omega
  · unfold Drum.highCoefficient; split
    all_goals try decide
    all_goals try omega
    · have q : (Drum.band colour >>> 2).toNat = (Drum.band colour).toNat / 4 := by
        rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
      omega
    · have q : (Drum.band colour >>> 3).toNat = (Drum.band colour).toNat / 8 := by
        rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
      omega
  · unfold Drum.lowCoefficient; split <;> decide

/-- Each shape's tail from a full envelope at its nominal rate, stepped sample by sample in the kernel: the
first sample at which the envelope is under a hundredth, with the sample before still above. BD (rate 219)
in 21984 samples (0.50 s), SD and the clap's tail (729) in 6617 (0.15 s), CH (2200) in 2193 (50 ms), OH
(270) in 17842 (0.40 s), LT (365) in 13206 (0.30 s), MT (437) in 11033 (0.25 s), HT and CB (547) in 8817
(0.20 s), CY (73) in 65568 (1.49 s).
Why it matters: these are the decay times a player hears, computed from the arithmetic the chip runs. -/
theorem drum_tails :
    (2 ^ 24 / 100 ≤ (Drum.envelopeAfter (2 ^ 24) (Drum.rate 0) 21983).toNat ∧
      (Drum.envelopeAfter (2 ^ 24) (Drum.rate 0) 21984).toNat < 2 ^ 24 / 100) ∧
    (2 ^ 24 / 100 ≤ (Drum.envelopeAfter (2 ^ 24) (Drum.rate 1) 6616).toNat ∧
      (Drum.envelopeAfter (2 ^ 24) (Drum.rate 1) 6617).toNat < 2 ^ 24 / 100) ∧
    (2 ^ 24 / 100 ≤ (Drum.envelopeAfter (2 ^ 24) (Drum.rate 3) 2192).toNat ∧
      (Drum.envelopeAfter (2 ^ 24) (Drum.rate 3) 2193).toNat < 2 ^ 24 / 100) ∧
    (2 ^ 24 / 100 ≤ (Drum.envelopeAfter (2 ^ 24) (Drum.rate 4) 17841).toNat ∧
      (Drum.envelopeAfter (2 ^ 24) (Drum.rate 4) 17842).toNat < 2 ^ 24 / 100) ∧
    (2 ^ 24 / 100 ≤ (Drum.envelopeAfter (2 ^ 24) (Drum.rate 5) 13205).toNat ∧
      (Drum.envelopeAfter (2 ^ 24) (Drum.rate 5) 13206).toNat < 2 ^ 24 / 100) ∧
    (2 ^ 24 / 100 ≤ (Drum.envelopeAfter (2 ^ 24) (Drum.rate 6) 11032).toNat ∧
      (Drum.envelopeAfter (2 ^ 24) (Drum.rate 6) 11033).toNat < 2 ^ 24 / 100) ∧
    (2 ^ 24 / 100 ≤ (Drum.envelopeAfter (2 ^ 24) (Drum.rate 7) 8816).toNat ∧
      (Drum.envelopeAfter (2 ^ 24) (Drum.rate 7) 8817).toNat < 2 ^ 24 / 100) ∧
    (2 ^ 24 / 100 ≤ (Drum.envelopeAfter (2 ^ 24) (Drum.rate 9) 65567).toNat ∧
      (Drum.envelopeAfter (2 ^ 24) (Drum.rate 9) 65568).toNat < 2 ^ 24 / 100) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
