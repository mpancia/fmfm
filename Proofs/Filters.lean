import Firmware.Filters
import Proofs.Digital

/-- An `Int32` shifted right 8 places is its value divided by 256, rounded down. -/
private theorem filters_shift_eight (s : Int32) : (s >>> 8).toInt = s.toInt / 256 := by
  have : (s >>> 8).toInt = s.toInt >>> 8 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (8 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- One saw, as the top 13 bits of its phase, is between 0 and 8191. -/
private theorem filters_saw_bound (p : UInt32) :
    (p >>> 19).toInt32.toInt ≤ 8191 ∧ 0 ≤ (p >>> 19).toInt32.toInt := by
  have h : (p >>> 19).toNat < 2 ^ 13 := by
    rw [UInt32.toNat_shiftRight]
    have : (UInt32.toNat 19 % 32) = 19 := by decide
    rw [this, Nat.shiftRight_eq_div_pow]
    have := p.toNat_lt
    omega
  have e : (p >>> 19).toInt32.toInt = ((p >>> 19).toNat : Int) := by
    show (p >>> 19).toBitVec.toInt = _
    rw [BitVec.toInt_eq_toNat_of_lt]
    · simp
    · simp at h ⊢; omega
  omega

/-- The sum of the swarm's seven saws lies between -28672 and 28665, whatever the phases.
Why it matters: the sum is handed to the overdrive shaper offset by 32768 with no mask, so this is what keeps
that read inside the shaper's 257 entries (`tables_shape_reads_inside_257`). -/
theorem filters_swarm_sum_range (p0 p1 p2 p3 p4 p5 p6 : UInt32) :
    -28672 ≤ (Filters.swarmSum p0 p1 p2 p3 p4 p5 p6).toInt ∧
      (Filters.swarmSum p0 p1 p2 p3 p4 p5 p6).toInt ≤ 28665 := by
  unfold Filters.swarmSum
  have := filters_saw_bound p0; have := filters_saw_bound p1; have := filters_saw_bound p2
  have := filters_saw_bound p3; have := filters_saw_bound p4; have := filters_saw_bound p5
  have := filters_saw_bound p6
  simp only [Int32.toInt_add]
  simp [Int.bmod_def]
  omega

/-- A harmonic's amplitude moves toward its target and never passes it (shown for an amplitude below its
target; the other direction is symmetric), for values within a quarter of the 32-bit range.
Why it matters: when a harmonic is told to fade, it fades monotonically; it cannot overshoot and ring. -/
theorem filters_harmonic_glide_approaches (amplitude target : Int32)
    (lo : -1073741824 < amplitude.toInt) (hi : target.toInt ≤ 1073741824)
    (order : amplitude.toInt ≤ target.toInt) :
    amplitude.toInt ≤ (Filters.harmonicGlide amplitude target).toInt ∧
      (Filters.harmonicGlide amplitude target).toInt ≤ target.toInt := by
  unfold Filters.harmonicGlide
  have d : (target - amplitude).toInt = target.toInt - amplitude.toInt := by
    rw [Int32.toInt_sub]
    simp [Int.bmod_def]
    split <;> omega
  rw [Int32.toInt_add, filters_shift_eight, d]
  simp [Int.bmod_def]
  split <;> omega


/-- An `Int32` shifted right one place is its value halved, rounded down. -/
private theorem filters_shift_one (s : Int32) : (s >>> 1).toInt = s.toInt / 2 := by
  have : (s >>> 1).toInt = s.toInt >>> 1 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (1 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- An `Int32` shifted right two places is its value divided by 4, rounded down. -/
private theorem filters_shift_two (s : Int32) : (s >>> 2).toInt = s.toInt / 4 := by
  have : (s >>> 2).toInt = s.toInt >>> 2 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (2 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- An `Int32` shifted right 15 places is its value divided by 32768, rounded down. -/
private theorem filters_shift_fifteen (s : Int32) : (s >>> 15).toInt = s.toInt / 32768 := by
  have : (s >>> 15).toInt = s.toInt >>> 15 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (15 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- An `Int32` shifted right 16 places is its value divided by 65536, rounded down. -/
private theorem filters_shift_sixteen (s : Int32) : (s >>> 16).toInt = s.toInt / 65536 := by
  have : (s >>> 16).toInt = s.toInt >>> 16 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (16 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- An `Int32` value in 16-bit range survives the cut to 16 bits. -/
private theorem filters_keep16 (x : Int32) (lo : -32768 ≤ x.toInt) (hi : x.toInt ≤ 32767) :
    x.toInt16.toInt = x.toInt := by
  rw [Int32.toInt_toInt16]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A value cut to 16 bits and widened again lies between -32768 and 32767. -/
private theorem filters_cut16_range (x : Int32) :
    -32768 ≤ x.toInt16.toInt32.toInt ∧ x.toInt16.toInt32.toInt ≤ 32767 := by
  rw [Int16.toInt_toInt32, Int32.toInt_toInt16]
  have lo := Int.le_bmod (x := x.toInt) (m := 2 ^ 16) (by decide)
  have hi := Int.bmod_lt (x := x.toInt) (m := 2 ^ 16) (by decide)
  omega

/-- A blended sine is a 16-bit value. -/
private theorem filters_sine_range (phase : UInt32) :
    -32768 ≤ (Analog.sineAt phase).toInt ∧ (Analog.sineAt phase).toInt ≤ 32767 := by
  unfold Analog.sineAt
  exact filters_cut16_range _

/-- A `UInt32` below 2^31 keeps its value as an `Int32`. -/
private theorem filters_small_toInt32 (x : UInt32) (below : x.toNat < 2 ^ 31) :
    x.toInt32.toInt = (x.toNat : Int) := by
  show x.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · simp
  · simp at below ⊢; omega

/-- The saw swarm's high-pass writes exactly its clipped output, between -32767 and 32767.
Why it matters: the swarm's final sample is limited by the clip and only the clip; a resonance peak can never
wrap around into a click. -/
theorem filters_swarm_filter_never_wraps (sample f damp bp lp : Int32) :
    (Filters.swarmFilter sample f damp bp lp).out.toInt =
      (Digital.clip ((sample - ((bp * damp) >>> 15)) - Digital.clip (lp + ((f * bp) >>> 15)))).toInt ∧
      -32767 ≤ (Filters.swarmFilter sample f damp bp lp).out.toInt ∧
        (Filters.swarmFilter sample f damp bp lp).out.toInt ≤ 32767 := by
  unfold Filters.swarmFilter
  dsimp only
  have := digital_clip_never_wraps ((sample - ((bp * damp) >>> 15)) - Digital.clip (lp + ((f * bp) >>> 15)))
  rw [this.1]
  exact ⟨rfl, this.2⟩

/-- A 16-bit carrier times a window of 0 to 65535 fits a signed 32-bit number. -/
private theorem filters_plain_product (carrier window : Int)
    (carrier16 : -32768 ≤ carrier ∧ carrier ≤ 32767) (window16 : 0 ≤ window ∧ window ≤ 65535) :
    -2147450880 ≤ carrier * window ∧ carrier * window ≤ 2147385345 := by
  have := Int.mul_le_mul_of_nonneg_right carrier16.2 window16.1
  have := Int.mul_le_mul_of_nonneg_right carrier16.1 window16.1
  have e1 : (32767 : Int) * window ≤ 32767 * 65535 := Int.mul_le_mul_of_nonneg_left window16.2 (by decide)
  have e2 : (-32768 : Int) * 65535 ≤ -32768 * window := Int.mul_le_mul_of_nonpos_left (by decide) window16.2
  omega

/-- The lifted window product `P` (0 to 65535 squared), wrapped to 32 bits, shifted down 16 places, centred
and read as 16 bits, is the intended `P / 65536 - 32768`. -/
private theorem filters_lifted_cancels (P : Int) (lo : 0 ≤ P) (hi : P ≤ 4294836225) :
    ((P.bmod (2 ^ 32) / 65536 - 32768).bmod (2 ^ 32)).bmod (2 ^ 16) = P / 65536 - 32768 := by
  by_cases half : P < 2 ^ 31
  · rw [Int.bmod_eq_of_le (n := P) (by omega) (by omega),
      Int.bmod_eq_of_le (n := P / 65536 - 32768) (by omega) (by omega)]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  · have wrapped : P.bmod (2 ^ 32) = P - 2 ^ 32 := by
      rw [← Int.sub_bmod_right]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    rw [wrapped, Int.bmod_eq_of_le (n := (P - 2 ^ 32) / 65536 - 32768) (by omega) (by omega),
      ← Int.add_bmod_right, Int.bmod_eq_of_le (by omega) (by omega)]
    omega

/-- The windowed carrier of the digital filter engines is the exact product the formula means, for a 16-bit
carrier and a window of 0 to 65535. In the low-pass and peak types the product can pass 2^31 and wrap (Braids'
C++ does the same); the read as a 16-bit value cancels the wrap exactly.
Why it matters: the saw or triangle voice of the digital filter engines never puts out a wrapped value, at any
pitch, cutoff or window position; the overflow in the original is proved harmless rather than assumed. -/
theorem filters_windowed_carrier_never_wraps (carrier window : Int32) (filterType : UInt8)
    (carrier16 : -32768 ≤ carrier.toInt ∧ carrier.toInt ≤ 32767)
    (window16 : 0 ≤ window.toInt ∧ window.toInt ≤ 65535) :
    (Filters.windowedCarrier carrier window filterType).toInt =
      if filterType &&& 2 != 0 then carrier.toInt * window.toInt / 65536
      else window.toInt * (carrier.toInt + 32768) / 65536 - 32768 := by
  unfold Filters.windowedCarrier
  split
  · have small := filters_plain_product carrier.toInt window.toInt carrier16 window16
    have product : (carrier * window).toInt = carrier.toInt * window.toInt := by
      rw [Int32.toInt_mul]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    rw [Int16.toInt_toInt32, Int32.toInt_toInt16, filters_shift_sixteen, product]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  · have lifted : (carrier + 32768).toInt = carrier.toInt + 32768 := by
      rw [Int32.toInt_add]
      have : Int32.toInt 32768 = 32768 := by decide
      rw [this]
      exact Int.bmod_eq_of_le (by omega) (by omega)
    have small : 0 ≤ window.toInt * (carrier.toInt + 32768) ∧
        window.toInt * (carrier.toInt + 32768) ≤ 4294836225 := by
      have := Int.mul_le_mul window16.2 (by omega : carrier.toInt + 32768 ≤ 65535) (by omega) (by decide)
      have := Int.mul_nonneg window16.1 (by omega : 0 ≤ carrier.toInt + 32768)
      omega
    have product : (window * (carrier + 32768)).toInt =
        (window.toInt * (carrier.toInt + 32768)).bmod (2 ^ 32) := by
      rw [Int32.toInt_mul, lifted]
    rw [Int16.toInt_toInt32, Int32.toInt_toInt16, Int32.toInt_sub, filters_shift_sixteen, product]
    have : Int32.toInt 32768 = 32768 := by decide
    rw [this]
    exact filters_lifted_cancels _ small.1 small.2

/-- Half the bell window is between 0 and 32767 at any phase. -/
private theorem filters_bell_half_range (phase : UInt32) :
    0 ≤ ((Filters.bellAt phase).toInt32 >>> 1).toInt ∧
      ((Filters.bellAt phase).toInt32 >>> 1).toInt ≤ 32767 := by
  unfold Filters.bellAt Digital.lutAt
  dsimp only
  generalize (Filters.bellTable (Analog.tableIndex phase)).toUInt32 +
    (((Filters.bellTable (Analog.tableIndex phase + 1)).toUInt32 -
      (Filters.bellTable (Analog.tableIndex phase)).toUInt32) * ((phase >>> 8) &&& 0xFFFF)) >>> 16 = raw
  have small : raw.toUInt16.toUInt32.toNat ≤ 65535 := by
    rw [UInt16.toNat_toUInt32, UInt32.toNat_toUInt16]
    omega
  rw [filters_shift_one, filters_small_toInt32 _ (by omega)]
  omega

/-- The vosim formant sum (24576 plus half a sine plus a quarter of a sine) is between 0 and 49150 and exact
in 32 bits. -/
private theorem filters_vosim_sample (a b : Int32) (ha : -32768 ≤ a.toInt ∧ a.toInt ≤ 32767)
    (hb : -32768 ≤ b.toInt ∧ b.toInt ≤ 32767) :
    ((24576 : Int32) + (a >>> 1) + (b >>> 2)).toInt = 24576 + a.toInt / 2 + b.toInt / 4 ∧
      0 ≤ 24576 + a.toInt / 2 + b.toInt / 4 ∧ 24576 + a.toInt / 2 + b.toInt / 4 ≤ 49150 := by
  rw [Int32.toInt_add, Int32.toInt_add, filters_shift_one, filters_shift_two]
  have : Int32.toInt 24576 = 24576 := by decide
  rw [this, Int.bmod_eq_of_le (n := 24576 + a.toInt / 2) (by omega) (by omega)]
  exact ⟨Int.bmod_eq_of_le (by omega) (by omega), by omega, by omega⟩

/-- A value of 0 to 49150 times a window of 0 to 32767 is exact in 32 bits, and shifted down 15 places it is
between 0 and 49150. -/
private theorem filters_vosim_window (sample w : Int) (hs : 0 ≤ sample ∧ sample ≤ 49150)
    (hw : 0 ≤ w ∧ w ≤ 32767) :
    (sample * w).bmod (2 ^ 32) = sample * w ∧ 0 ≤ sample * w / 32768 ∧ sample * w / 32768 ≤ 49150 := by
  have := Int.mul_le_mul hs.2 hw.2 hw.1 (by decide)
  have := Int.mul_nonneg hs.1 hw.1
  exact ⟨Int.bmod_eq_of_le (by omega) (by omega), by omega, by omega⟩

/-- Centring a value of 0 to 49150 on 24576 is exact in 32 bits and fits 16 bits. -/
private theorem filters_vosim_centre (v : Int32) (hv : 0 ≤ v.toInt ∧ v.toInt ≤ 49150) :
    (v - 24576).toInt = v.toInt - 24576 ∧ -32768 ≤ v.toInt - 24576 ∧ v.toInt - 24576 ≤ 32767 := by
  rw [Int32.toInt_sub]
  have : Int32.toInt 24576 = 24576 := by decide
  rw [this]
  exact ⟨Int.bmod_eq_of_le (by omega) (by omega), by omega, by omega⟩

/-- Vosim writes exactly its windowed formant sum, centred on zero: the two formants under the bell window
never pass 49150 before the centring, so nothing wraps, at any pitch or formant setting.
Why it matters: vosim cannot click from an overflow, whatever the two formant frequencies are. -/
theorem filters_vosim_never_wraps (phase inc formant0 formant1 inc0 inc1 : UInt32) (sync : UInt8) :
    (Filters.vosim phase inc formant0 formant1 inc0 inc1 sync).out.toInt =
      (if (if sync != 0 then 0 else phase + inc) < inc then (0 : Int32) else
        (((24576 : Int32) + (Analog.sineAt (formant0 + inc0) >>> 1) +
          (Analog.sineAt (formant1 + inc1) >>> 2)) *
          ((Filters.bellAt (if sync != 0 then 0 else phase + inc)).toInt32 >>> 1)) >>> 15).toInt - 24576 := by
  unfold Filters.vosim
  dsimp only
  generalize (if sync != 0 then 0 else phase + inc) = p
  have bell := filters_bell_half_range p
  obtain ⟨sample, lo, hi⟩ := filters_vosim_sample (Analog.sineAt (formant0 + inc0))
    (Analog.sineAt (formant1 + inc1)) (filters_sine_range _) (filters_sine_range _)
  generalize Analog.sineAt (formant0 + inc0) = a at *
  generalize Analog.sineAt (formant1 + inc1) = b at *
  generalize (Filters.bellAt p).toInt32 >>> 1 = w at *
  generalize (24576 : Int32) + (a >>> 1) + (b >>> 2) = s at *
  generalize 24576 + a.toInt / 2 + b.toInt / 4 = sv at *
  obtain ⟨product, wlo, whi⟩ := filters_vosim_window sv w.toInt ⟨lo, hi⟩ bell
  have windowed : ((s * w) >>> 15).toInt = sv * w.toInt / 32768 := by
    rw [filters_shift_fifteen, Int32.toInt_mul, sample, product]
  generalize (s * w) >>> 15 = v at *
  have value : 0 ≤ (if p < inc then (0 : Int32) else v).toInt ∧
      (if p < inc then (0 : Int32) else v).toInt ≤ 49150 := by
    split
    · decide
    · omega
  obtain ⟨centre, clo, chi⟩ := filters_vosim_centre _ value
  rw [filters_keep16 _ (by omega) (by omega), centre]

/-- The harmonics engine writes exactly its clipped sum, and the in-between sample exactly the average of that
with the last sample.
Why it matters: adding the harmonics is limited by the clip and only the clip, and the half-rate smoothing
cannot wrap, so the engine cannot click from an overflow. -/
theorem filters_harmonics_never_wraps (sum previous : Int32)
    (previous16 : -32768 ≤ previous.toInt ∧ previous.toInt ≤ 32767) :
    (Filters.harmonicsOut sum).toInt16.toInt = (Digital.clip sum).toInt ∧
      (Filters.harmonicsMid sum previous).toInt16.toInt =
        ((Digital.clip sum).toInt + previous.toInt) / 2 := by
  unfold Filters.harmonicsOut Filters.harmonicsMid
  obtain ⟨written, lo, hi⟩ := digital_clip_never_wraps sum
  refine ⟨written, ?_⟩
  generalize Digital.clip sum = c at *
  have added : (c + previous).toInt = c.toInt + previous.toInt := by
    rw [Int32.toInt_add]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have halved : ((c + previous) >>> 1).toInt = (c.toInt + previous.toInt) / 2 := by
    rw [filters_shift_one, added]
  rw [filters_keep16 _ (by omega) (by omega), halved]
