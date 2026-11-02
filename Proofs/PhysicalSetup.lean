import Firmware.PhysicalSetup

/-!
The block setup of the physical models hands the sample loops (`Proofs/Physical.lean`) the sizes, positions
and table indexes they index their lines and tables with. These theorems show those numbers are the ones the
line theorems assume, so their hypotheses about "what the C++ sets" are met by construction.
-/

/-- A 32-bit product whose true value fits is exact. -/
private theorem physical_setup_mul_exact (a b : Int32) (fits : (a.toInt * b.toInt).natAbs < 2 ^ 31) :
    (a * b).toInt = a.toInt * b.toInt := by
  rw [Int32.toInt_mul]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A 32-bit addition whose true sum fits is exact. -/
private theorem physical_setup_add_exact (a b : Int32) (fits : (a.toInt + b.toInt).natAbs < 2 ^ 31) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add]; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- An `Int32` shifted right one place is its value halved, rounded down. -/
private theorem physical_setup_shift_one (s : Int32) : (s >>> 1).toInt = s.toInt / 2 := by
  show (s >>> 1).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- The same by seven places. -/
private theorem physical_setup_shift_seven (s : Int32) : (s >>> 7).toInt = s.toInt / 128 := by
  show (s >>> 7).toBitVec.toInt = _
  rw [Int32.toBitVec_shiftRight, BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]; rfl

/-- A signed value between 0 and 65535 keeps its value as an unsigned one. -/
private theorem physical_setup_small_toUInt32 (p : Int32) (lo : 0 ≤ p.toInt) (hi : p.toInt ≤ 65535) :
    p.toUInt32.toNat = p.toInt.toNat := by
  have e : p.toInt = p.toBitVec.toInt := rfl
  have n : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [BitVec.toInt_eq_toNat_cond] at e
  rw [n]
  have := BitVec.isLt p.toBitVec
  split at e <;> omega

/-- A `UInt32` shifted right is its value divided by that power of two, for shifts below 32. -/
private theorem physical_setup_ushift (x n : UInt32) (small : n.toNat < 32) :
    (x >>> n).toNat = x.toNat / 2 ^ n.toNat := by
  rw [UInt32.toNat_shiftRight, Nat.mod_eq_of_lt small, Nat.shiftRight_eq_div_pow]

/-- One step of the oversampling search adds at most one to a count of at most 8. -/
private theorem physical_setup_pluck_step (increment n : UInt32) (k : Nat) (small : k ≤ 8)
    (counted : n.toNat ≤ k) : (PhysicalSetup.pluckShiftStep increment n).toNat ≤ k + 1 := by
  unfold PhysicalSetup.pluckShiftStep
  split
  · rw [UInt32.toNat_add]; simp; omega
  · omega

/-- The oversampling search counts at most nine halvings. -/
private theorem physical_setup_pluck_shift_le (increment : UInt32) :
    (PhysicalSetup.pluckShift increment).toNat ≤ 9 := by
  unfold PhysicalSetup.pluckShift
  dsimp only
  have s1 := physical_setup_pluck_step increment 0 0 (by omega) (by decide)
  have s2 := physical_setup_pluck_step increment _ 1 (by omega) s1
  have s3 := physical_setup_pluck_step increment _ 2 (by omega) s2
  have s4 := physical_setup_pluck_step increment _ 3 (by omega) s3
  have s5 := physical_setup_pluck_step increment _ 4 (by omega) s4
  have s6 := physical_setup_pluck_step increment _ 5 (by omega) s5
  have s7 := physical_setup_pluck_step increment _ 6 (by omega) s6
  have s8 := physical_setup_pluck_step increment _ 7 (by omega) s7
  exact physical_setup_pluck_step increment _ 8 (by omega) s8

/-- The width of a new string's noise fill, 8192 plus three halves of `param1`, is below 65536. -/
private theorem physical_setup_pluck_width (param1 : Int32) (fits : 0 ≤ param1.toInt ∧ param1.toInt ≤ 32767) :
    ((8192 : Int32) + ((3 : Int32) * param1) >>> 1).toUInt32.toNat ≤ 57342 := by
  have c3 : (3 : Int32).toInt = 3 := by decide
  have c8192 : (8192 : Int32).toInt = 8192 := by decide
  have triple : ((3 : Int32) * param1).toInt = 3 * param1.toInt := by
    rw [physical_setup_mul_exact _ _ (by rw [c3]; omega), c3]
  have half := physical_setup_shift_one ((3 : Int32) * param1)
  rw [triple] at half
  have sum : ((8192 : Int32) + ((3 : Int32) * param1) >>> 1).toInt = 8192 + (3 * param1.toInt) / 2 := by
    rw [physical_setup_add_exact _ _ (by rw [c8192, half]; omega), c8192, half]
  rw [physical_setup_small_toUInt32 _ (by rw [sum]; omega) (by rw [sum]; omega), sum]
  omega

/-- A new plucked string meets the line theorems' hypotheses: its oversampling is at most 9 (`oversampled` in
`physical_pluck_read_in_line` and `physical_pluck_next_in_line`; `pluckSize` and `pluckMask` are
`1024 >>> shift` and `size - 1` by definition), and its fill count is at most its size (`fits` in
`physical_pluck_fill_in_line`; the glue only fills while the count is nonzero, that theorem's `started`).
Holds for `param1` from 0 to 32767.
Why it matters: these numbers decide where the plucked string reads and writes its 1025-entry line. -/
theorem physical_setup_pluck_size_valid (increment : UInt32) (param1 : Int32)
    (param1Fits : 0 ≤ param1.toInt ∧ param1.toInt ≤ 32767) :
    PhysicalSetup.pluckShift increment ≤ 9 ∧
      PhysicalSetup.pluckInitialization (PhysicalSetup.pluckShift increment) param1 ≤
        PhysicalSetup.pluckSize (PhysicalSetup.pluckShift increment) := by
  have shiftLe := physical_setup_pluck_shift_le increment
  refine ⟨UInt32.le_iff_toNat_le.mpr shiftLe, ?_⟩
  generalize PhysicalSetup.pluckShift increment = shift at shiftLe
  have width := physical_setup_pluck_width param1 param1Fits
  unfold PhysicalSetup.pluckInitialization PhysicalSetup.pluckSize
  dsimp only
  generalize ((8192 : Int32) + ((3 : Int32) * param1) >>> 1).toUInt32 = w at width
  have size : (1024 >>> shift : UInt32).toNat = 1024 / 2 ^ shift.toNat := physical_setup_ushift _ _ (by omega)
  have sizeLe : (1024 >>> shift : UInt32).toNat ≤ 1024 := by rw [size]; exact Nat.div_le_self _ _
  generalize (1024 >>> shift : UInt32) = s at size sizeLe
  have product : (s * w).toNat = s.toNat * w.toNat := by
    rw [UInt32.toNat_mul]
    exact Nat.mod_eq_of_lt (by have := Nat.mul_le_mul sizeLe width; omega)
  rw [UInt32.le_iff_toNat_le, physical_setup_ushift _ _ (by decide), product]
  show s.toNat * w.toNat / 2 ^ 16 ≤ s.toNat
  have le : s.toNat * w.toNat ≤ 2 ^ 16 * s.toNat := by
    rw [Nat.mul_comm (2 ^ 16)]; exact Nat.mul_le_mul_left _ (by omega)
  exact Nat.div_le_of_le_mul le

/-- The comb filter's whole-sample delay is at most 8192, its line's length.
Why it matters: the positions are masked, so a longer delay would not read outside the line but would read
the wrong sample; the clamp is the only thing preventing it. -/
theorem physical_setup_comb_delay_in_line (delay : UInt32) :
    (PhysicalSetup.combDelayIntegral delay).toNat ≤ 8192 := by
  unfold PhysicalSetup.combDelayIntegral PhysicalSetup.combDelay
  have sixteen : (2 : Nat) ^ (16 : UInt32).toNat = 65536 := by decide
  rw [physical_setup_ushift _ _ (by decide), sixteen]
  split
  · decide
  · rename_i h
    rw [UInt32.not_lt, UInt32.le_iff_toNat_le] at h
    have top : (8192 * 65536 : UInt32).toNat = 536870912 := by decide
    rw [top] at h
    omega

/-- The bowing and blowing envelope pointers a block leaves behind read inside their envelopes through the
next block: the bowed string's pointer is held to 1440, so its two reads (at half the pointer and half the
pointer plus one) stay below the 752-entry bowing envelope for any advance up to 16 samples, and the flute's
is held to 360, so its read stays below the 392-entry blowing envelope. A block is 16 samples; the bowed
string advances one per two samples, the flute three per four.
Why it matters: both envelopes are read unchecked at the pointer; the clamp after each block keeps a long
note from running off the end. -/
theorem physical_setup_envelope_pointer_in_table (ptr advance : UInt32) (block : advance ≤ 16) :
    ((PhysicalSetup.bowedExcitationClamp ptr + advance + 1) >>> 1).toNat < 752 ∧
      (PhysicalSetup.flutedExcitationClamp ptr + advance).toNat < 392 := by
  have advanceLe : advance.toNat ≤ 16 := UInt32.le_iff_toNat_le.mp block
  have kept : ptr.toUInt16.toUInt32.toNat ≤ 65535 := by
    rw [UInt16.toNat_toUInt32]; have := ptr.toUInt16.toNat_lt; omega
  constructor
  · unfold PhysicalSetup.bowedExcitationClamp
    dsimp only
    generalize ptr.toUInt16.toUInt32 = k at kept
    have one : (1 : UInt32).toNat = 1 := by decide
    have two : (2 : Nat) ^ (1 : UInt32).toNat = 2 := by decide
    have c1440 : (1440 : UInt32).toNat = 1440 := by decide
    have c720 : (720 : UInt32).toNat = 720 := by decide
    rw [physical_setup_ushift _ _ (by decide), UInt32.toNat_add, UInt32.toNat_add, one]
    split
    · rw [c1440]; omega
    · rename_i h
      rw [UInt32.not_le, UInt32.lt_iff_toNat_lt, physical_setup_ushift _ _ (by decide), c720, two] at h
      omega
  · unfold PhysicalSetup.flutedExcitationClamp
    dsimp only
    generalize ptr.toUInt16.toUInt32 = k at kept
    have c360 : (360 : UInt32).toNat = 360 := by decide
    rw [UInt32.toNat_add]
    split
    · rw [c360]; omega
    · rename_i h
      rw [UInt32.not_le, UInt32.lt_iff_toNat_lt, c360] at h
      omega

/-- A clamp of an `Int32` to 0 to 127 lands in 0 to 127. -/
private theorem physical_setup_note_clamped (note : Int32) :
    0 ≤ (if note < 0 then (0 : Int32) else if note > 127 then 127 else note).toInt ∧
      (if note < 0 then (0 : Int32) else if note > 127 then 127 else note).toInt ≤ 127 := by
  split
  · simp
  · split
    · simp
    · rename_i a b
      simp only [gt_iff_lt] at b
      rw [Int32.lt_iff_toInt_lt] at a b
      have c0 : (0 : Int32).toInt = 0 := by decide
      have c127 : (127 : Int32).toInt = 127 := by decide
      rw [c0] at a
      rw [c127] at b
      omega

/-- The blown pipe and the flute read their body filter inside its 128-entry table, for any pitch and
parameter.
Why it matters: Braids indexes this table by the pitch in semitones, which can reach note 140; the clamp to
127 keeps the read inside. -/
theorem physical_setup_flute_body_in_table (pitch param1 : Int32) :
    (PhysicalSetup.blownNormalizedPitch pitch param1).toUInt32.toNat ≤ 127 ∧
      (PhysicalSetup.flutedNote pitch).toUInt32.toNat ≤ 127 := by
  constructor
  · unfold PhysicalSetup.blownNormalizedPitch
    dsimp only
    have ⟨lo, hi⟩ :=
      physical_setup_note_clamped (((pitch - (8192 : Int32) + param1 >>> 1) >>> 7).toInt16.toInt32)
    rw [physical_setup_small_toUInt32 _ lo (by omega)]
    omega
  · unfold PhysicalSetup.flutedNote
    dsimp only
    have ⟨lo, hi⟩ := physical_setup_note_clamped (pitch >>> 7)
    rw [physical_setup_small_toUInt32 _ lo (by omega)]
    omega
