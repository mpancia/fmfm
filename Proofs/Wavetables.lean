import Firmware.Wavetables
import Proofs.Blend

/-- An `Int32` shifted right one place is its value halved, rounded down. -/
private theorem wavetables_shift_one (s : Int32) : (s >>> 1).toInt = s.toInt / 2 := by
  have : (s >>> 1).toInt = s.toInt >>> 1 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (1 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- A crossfade of two waves is a 16-bit value. -/
private theorem wavetables_crossfade_range (waveA waveB phase balance : UInt32) :
    -32768 ≤ (Wavetables.crossfade waveA waveB phase balance).toInt ∧
      (Wavetables.crossfade waveA waveB phase balance).toInt ≤ 32767 := by
  unfold Wavetables.crossfade
  dsimp only
  rw [Int16.toInt_toInt32, Int32.toInt_toInt16]
  simp [Int.bmod_def]
  split <;> omega

/-- A wavetable sample is exactly the sum of its two half-rate readings, each halved: nothing wraps around.
Why it matters: the wavetable engine cannot click from an overflow, for any waves, phase or morph position. -/
theorem wavetables_wavetable_never_wraps (phase inc waveA waveB balance : UInt32) (sync : UInt8) :
    (Wavetables.wavetable phase inc waveA waveB balance sync).out.toInt =
      (Wavetables.crossfade waveA waveB ((if sync != 0 then 0 else phase + inc) >>> 1) balance).toInt / 2 +
      (Wavetables.crossfade waveA waveB (((if sync != 0 then 0 else phase + inc) + inc) >>> 1)
        balance).toInt / 2 := by
  unfold Wavetables.wavetable
  dsimp only
  generalize hs : (if sync != 0 then 0 else phase + inc) = start
  have h1 := wavetables_crossfade_range waveA waveB (start >>> 1) balance
  have h2 := wavetables_crossfade_range waveA waveB ((start + inc) >>> 1) balance
  generalize Wavetables.crossfade waveA waveB (start >>> 1) balance = a at *
  generalize Wavetables.crossfade waveA waveB ((start + inc) >>> 1) balance = b at *
  rw [Int32.toInt_toInt16, Int32.toInt_add, wavetables_shift_one, wavetables_shift_one]
  simp [Int.bmod_def]
  split <;> omega

/-- A crossfade of two waves at the same phase lies between the two waves' values there, for any two waves.
Why it matters: morphing between waves can never be louder than the louder wave, at any morph position, even
where the two waves are far apart (where Braids' C++ product wraps; see `blend_sixteen_between`). -/
theorem wavetables_crossfade_between_waves (waveA waveB phase balance : UInt32) :
    min (Wavetables.read waveA phase).toInt (Wavetables.read waveB phase).toInt ≤
        (Wavetables.crossfade waveA waveB phase balance).toInt ∧
      (Wavetables.crossfade waveA waveB phase balance).toInt ≤
        max (Wavetables.read waveA phase).toInt (Wavetables.read waveB phase).toInt := by
  have ra : -32768 ≤ (Wavetables.read waveA phase).toInt ∧ (Wavetables.read waveA phase).toInt ≤ 32767 := by
    unfold Wavetables.read; dsimp only
    rw [Int16.toInt_toInt32, Int32.toInt_toInt16]; simp [Int.bmod_def]; split <;> omega
  have rb : -32768 ≤ (Wavetables.read waveB phase).toInt ∧ (Wavetables.read waveB phase).toInt ≤ 32767 := by
    unfold Wavetables.read; dsimp only
    rw [Int16.toInt_toInt32, Int32.toInt_toInt16]; simp [Int.bmod_def]; split <;> omega
  unfold Wavetables.crossfade
  dsimp only
  exact blend_sixteen_between _ _ balance ra rb

/-- The low 24 bits of a value are at most 2^24 - 1. -/
private theorem wavetables_and_ffffff (x : UInt32) : (x &&& 0xFFFFFF).toNat ≤ 16777215 := by
  rw [UInt32.toNat_and]
  have := Nat.and_le_right (n := x.toNat) (m := (0xFFFFFF : UInt32).toNat)
  simpa using this

/-- A `UInt32` below 2^31 keeps its value as an `Int32`. -/
private theorem wavetables_small_toInt32 (x : UInt32) (below : x.toNat < 2 ^ 31) :
    x.toInt32.toInt = (x.toNat : Int) := by
  show x.toBitVec.toInt = _
  rw [BitVec.toInt_eq_toNat_of_lt]
  · simp
  · simp at below ⊢; omega

/-- An `Int32` shifted right 16 places is its value divided by 65536, rounded down. -/
private theorem wavetables_shift_sixteen (s : Int32) : (s >>> 16).toInt = s.toInt / 65536 := by
  have : (s >>> 16).toInt = s.toInt >>> 16 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (16 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- `d * f / 65536` for `0 ≤ f < 2^24` lies between 0 and `d * 256` (either way round). -/
private theorem wavetables_step (d f : Int) (hf : 0 ≤ f ∧ f ≤ 16777215) :
    (0 ≤ d * f / 65536 ∧ d * f / 65536 ≤ d * 256) ∨ (d * 256 ≤ d * f / 65536 ∧ d * f / 65536 ≤ 0) := by
  by_cases h : 0 ≤ d
  · left
    have u : d * f ≤ d * 16777216 := Int.mul_le_mul_of_nonneg_left (by omega) h
    have l : 0 ≤ d * f := Int.mul_nonneg h hf.1
    have u' := Int.ediv_le_ediv (by decide : (0 : Int) < 65536) u
    have e : d * 16777216 / 65536 = d * 256 := by
      rw [show (16777216 : Int) = 256 * 65536 by decide, ← Int.mul_assoc, Int.mul_ediv_cancel _ (by decide)]
    rw [e] at u'
    exact ⟨Int.ediv_nonneg l (by decide), u'⟩
  · right
    have neg : d ≤ 0 := by omega
    have l : d * 16777216 ≤ d * f := Int.mul_le_mul_of_nonpos_left neg (by omega)
    have u : d * f ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg neg hf.1
    have l' := Int.ediv_le_ediv (by decide : (0 : Int) < 65536) l
    have e : d * 16777216 / 65536 = d * 256 := by
      rw [show (16777216 : Int) = 256 * 65536 by decide, ← Int.mul_assoc, Int.mul_ediv_cancel _ (by decide)]
    rw [e] at l'
    exact ⟨l', Int.ediv_nonpos_of_nonpos_of_neg u (by decide)⟩

/-- A wave read lies between the two bytes it blends (each byte scaled to 16 bits), for any wave and phase.
The product inside wraps in 32 bits for steep waves (Braids' `wt_waves` has byte steps up to 253; the C++
does the same), and the cut to 16 bits cancels the wrap exactly.
Why it matters: a wave never puts out more than its bytes hold, and the overflow in the original is proved
harmless rather than assumed. -/
theorem wavetables_read_between_bytes (wave phase : UInt32) :
    min ((Wavetables.waveByte wave (Analog.tableIndex phase)).toNat * 256 - 32768 : Int)
        ((Wavetables.waveByte wave (Analog.tableIndex phase + 1)).toNat * 256 - 32768) ≤
        (Wavetables.read wave phase).toInt ∧
      (Wavetables.read wave phase).toInt ≤
        max ((Wavetables.waveByte wave (Analog.tableIndex phase)).toNat * 256 - 32768 : Int)
          ((Wavetables.waveByte wave (Analog.tableIndex phase + 1)).toNat * 256 - 32768) := by
  unfold Wavetables.read
  dsimp only
  generalize Wavetables.waveByte wave (Analog.tableIndex phase) = x
  generalize Wavetables.waveByte wave (Analog.tableIndex phase + 1) = y
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have f := wavetables_and_ffffff phase
  have ax : x.toUInt32.toInt32.toInt = (x.toNat : Int) := by
    rw [wavetables_small_toInt32 _ (by rw [UInt8.toNat_toUInt32]; omega), UInt8.toNat_toUInt32]
  have ay : y.toUInt32.toInt32.toInt = (y.toNat : Int) := by
    rw [wavetables_small_toInt32 _ (by rw [UInt8.toNat_toUInt32]; omega), UInt8.toNat_toUInt32]
  have t : (phase &&& 0xFFFFFF).toInt32.toInt = ((phase &&& 0xFFFFFF).toNat : Int) :=
    wavetables_small_toInt32 _ (by omega)
  have sh : (x.toUInt32.toInt32 * 256).toInt = (x.toNat : Int) * 256 := by
    rw [Int32.toInt_mul, ax]
    have : Int32.toInt 256 = 256 := by decide
    rw [this]
    simp [Int.bmod_def]
    omega
  have d : (y.toUInt32.toInt32 - x.toUInt32.toInt32).toInt = (y.toNat : Int) - x.toNat := by
    rw [Int32.toInt_sub, ay, ax]; simp [Int.bmod_def]; split <;> omega
  have st := wavetables_step ((y.toNat : Int) - x.toNat) ((phase &&& 0xFFFFFF).toNat : Int) (by omega)
  rw [Int16.toInt_toInt32, Int32.toInt_toInt16]
  have d' : ((y.toNat : Int) - x.toNat).bmod (2 ^ 32) = (y.toNat : Int) - x.toNat := by
    simp [Int.bmod_def]; split <;> omega
  simp only [Int32.toInt_sub, Int32.toInt_add, Int32.toInt_mul, sh, wavetables_shift_sixteen, ax, ay, t, d']
  generalize ((y.toNat : Int) - x.toNat) * ((phase &&& 0xFFFFFF).toNat : Int) = P at *
  have k : Int32.toInt 32768 = 32768 := by decide
  simp only [Int.bmod_def, k]
  split <;> split <;> split <;> split <;> omega

/-- An `Int32` shifted right two places is its value divided by 4, rounded down. -/
private theorem wavetables_shift_two (s : Int32) : (s >>> 2).toInt = s.toInt / 4 := by
  have : (s >>> 2).toInt = s.toInt >>> 2 := by
    show (s.toBitVec.sshiftRight' (BitVec.smod (2 : Int32).toBitVec 32)).toInt = _
    simp
  rw [this, Int.shiftRight_eq_div_pow]
  rfl

/-- A value cut to 16 bits and widened again lies between -32768 and 32767. -/
private theorem wavetables_cut16_range (x : Int32) :
    -32768 ≤ x.toInt16.toInt32.toInt ∧ x.toInt16.toInt32.toInt ≤ 32767 := by
  rw [Int16.toInt_toInt32, Int32.toInt_toInt16]
  have lo := Int.le_bmod (x := x.toInt) (m := 2 ^ 16) (by decide)
  have hi := Int.bmod_lt (x := x.toInt) (m := 2 ^ 16) (by decide)
  omega

/-- A mix of two values is a 16-bit value. -/
private theorem wavetables_mix_range (a b : Int32) (balance : UInt32) :
    -32768 ≤ (Digital.mix a b balance).toInt ∧ (Digital.mix a b balance).toInt ≤ 32767 := by
  unfold Digital.mix
  exact wavetables_cut16_range _

/-- An `Int32` value in 16-bit range survives the cut to 16 bits. -/
private theorem wavetables_keep16 (x : Int32) (lo : -32768 ≤ x.toInt) (hi : x.toInt ≤ 32767) :
    x.toInt16.toInt = x.toInt := by
  rw [Int32.toInt_toInt16]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- Adding two 16-bit values in 32 bits does not wrap. -/
private theorem wavetables_add16 (a b : Int32) (ha : -32768 ≤ a.toInt ∧ a.toInt ≤ 32767)
    (hb : -32768 ≤ b.toInt ∧ b.toInt ≤ 32767) : (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- One half-rate reading of a wave map is between -16384 and 16383. -/
private theorem wavetables_map_read_range (p w00 w01 w10 w11 xfadeX xfadeY : UInt32) :
    -16384 ≤ (Wavetables.mapRead p w00 w01 w10 w11 xfadeX xfadeY).toInt ∧
      (Wavetables.mapRead p w00 w01 w10 w11 xfadeX xfadeY).toInt ≤ 16383 := by
  unfold Wavetables.mapRead
  rw [wavetables_shift_one]
  have := wavetables_mix_range (Wavetables.crossfade w00 w01 (p >>> 1) xfadeY)
    (Wavetables.crossfade w10 w11 (p >>> 1) xfadeY) (xfadeX &&& 0xFFFF)
  omega

/-- A wave map sample is exactly the sum of its two half-rate readings, each already halved: nothing wraps
around.
Why it matters: the wave map engine cannot click from an overflow, for any square of the map, phase or
position inside the square. -/
theorem wavetables_wave_map_never_wraps (phase inc w00 w01 w10 w11 xfadeX xfadeY : UInt32) (sync : UInt8) :
    (Wavetables.waveMap phase inc w00 w01 w10 w11 xfadeX xfadeY sync).out.toInt =
      (Wavetables.mapRead (if sync != 0 then 0 else phase + inc) w00 w01 w10 w11 xfadeX xfadeY).toInt +
      (Wavetables.mapRead ((if sync != 0 then 0 else phase + inc) + inc) w00 w01 w10 w11 xfadeX
        xfadeY).toInt := by
  unfold Wavetables.waveMap
  dsimp only
  generalize (if sync != 0 then 0 else phase + inc) = start
  have first := wavetables_map_read_range start w00 w01 w10 w11 xfadeX xfadeY
  have second := wavetables_map_read_range (start + inc) w00 w01 w10 w11 xfadeX xfadeY
  generalize Wavetables.mapRead start w00 w01 w10 w11 xfadeX xfadeY = a at *
  generalize Wavetables.mapRead (start + inc) w00 w01 w10 w11 xfadeX xfadeY = b at *
  have sum := wavetables_add16 a b (by omega) (by omega)
  rw [wavetables_keep16 _ (by omega) (by omega), sum]

/-- A wave line half step is a 16-bit value. -/
private theorem wavetables_line_pair_range
    (phase waveA waveB xfadeA maskA waveC waveD xfadeB maskB balance : UInt32) :
    -32768 ≤ (Wavetables.linePair phase waveA waveB xfadeA maskA waveC waveD xfadeB maskB balance).toInt ∧
      (Wavetables.linePair phase waveA waveB xfadeA maskA waveC waveD xfadeB maskB balance).toInt ≤
        32767 := by
  unfold Wavetables.linePair
  exact wavetables_mix_range _ _ _

/-- A wave line sample is exactly the average of its two half steps: nothing wraps around.
Why it matters: the wave line engine cannot click from an overflow, for any waves, masks, crossfades or
balance. -/
theorem wavetables_wave_line_never_wraps
    (phase inc waveA waveB xfadeA stepA maskA waveC waveD xfadeB stepB maskB balance : UInt32)
    (sync : UInt8) :
    (Wavetables.waveLine phase inc waveA waveB xfadeA stepA maskA waveC waveD xfadeB stepB maskB balance
      sync).out.toInt =
      ((Wavetables.linePair (if sync != 0 then 0 else phase) waveA waveB xfadeA maskA waveC waveD xfadeB
          maskB balance).toInt +
        (Wavetables.linePair ((if sync != 0 then 0 else phase) + inc) waveA waveB
          ((xfadeA + stepA) &&& 0xFFFF) maskA waveC waveD ((xfadeB + stepB) &&& 0xFFFF) maskB
          balance).toInt) / 2 := by
  unfold Wavetables.waveLine
  dsimp only
  generalize (if sync != 0 then 0 else phase) = start
  have first := wavetables_line_pair_range start waveA waveB xfadeA maskA waveC waveD xfadeB maskB
    balance
  have second := wavetables_line_pair_range (start + inc) waveA waveB ((xfadeA + stepA) &&& 0xFFFF)
    maskA waveC waveD ((xfadeB + stepB) &&& 0xFFFF) maskB balance
  generalize Wavetables.linePair start waveA waveB xfadeA maskA waveC waveD xfadeB maskB balance = a at *
  generalize Wavetables.linePair (start + inc) waveA waveB ((xfadeA + stepA) &&& 0xFFFF) maskA waveC waveD
    ((xfadeB + stepB) &&& 0xFFFF) maskB balance = b at *
  have sum := wavetables_add16 a b first second
  have halved : ((a + b) >>> 1).toInt = (a.toInt + b.toInt) / 2 := by rw [wavetables_shift_one, sum]
  rw [wavetables_keep16 _ (by omega) (by omega), halved]

/-- Adding four 16-bit values in 32 bits does not wrap. -/
private theorem wavetables_add_four (a b c d : Int32) (ha : -32768 ≤ a.toInt ∧ a.toInt ≤ 32767)
    (hb : -32768 ≤ b.toInt ∧ b.toInt ≤ 32767) (hc : -32768 ≤ c.toInt ∧ c.toInt ≤ 32767)
    (hd : -32768 ≤ d.toInt ∧ d.toInt ≤ 32767) :
    (a + b + c + d).toInt = a.toInt + b.toInt + c.toInt + d.toInt := by
  have two := wavetables_add16 a b ha hb
  have three : (a + b + c).toInt = a.toInt + b.toInt + c.toInt := by
    rw [Int32.toInt_add, two]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  rw [Int32.toInt_add, three]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- A paraphonic sample is exactly the sum of its four voices divided by four: nothing wraps around.
Why it matters: four full-scale voices added in 32 bits stay far inside the range, so the chord engine cannot
click from an overflow at any chord, phase or morph position. -/
theorem wavetables_paraphonic_never_wraps (p0 p1 p2 p3 inc0 inc1 inc2 inc3 waveA waveB balance : UInt32) :
    (Wavetables.paraphonic p0 p1 p2 p3 inc0 inc1 inc2 inc3 waveA waveB balance).out.toInt =
      ((Wavetables.crossfade waveA waveB ((p0 + inc0) >>> 1) balance).toInt +
        (Wavetables.crossfade waveA waveB ((p1 + inc1) >>> 1) balance).toInt +
        (Wavetables.crossfade waveA waveB ((p2 + inc2) >>> 1) balance).toInt +
        (Wavetables.crossfade waveA waveB ((p3 + inc3) >>> 1) balance).toInt) / 4 := by
  unfold Wavetables.paraphonic
  dsimp only
  have r0 := wavetables_crossfade_range waveA waveB ((p0 + inc0) >>> 1) balance
  have r1 := wavetables_crossfade_range waveA waveB ((p1 + inc1) >>> 1) balance
  have r2 := wavetables_crossfade_range waveA waveB ((p2 + inc2) >>> 1) balance
  have r3 := wavetables_crossfade_range waveA waveB ((p3 + inc3) >>> 1) balance
  generalize Wavetables.crossfade waveA waveB ((p0 + inc0) >>> 1) balance = a at *
  generalize Wavetables.crossfade waveA waveB ((p1 + inc1) >>> 1) balance = b at *
  generalize Wavetables.crossfade waveA waveB ((p2 + inc2) >>> 1) balance = c at *
  generalize Wavetables.crossfade waveA waveB ((p3 + inc3) >>> 1) balance = d at *
  have sum := wavetables_add_four a b c d r0 r1 r2 r3
  have quartered : ((a + b + c + d) >>> 2).toInt = (a.toInt + b.toInt + c.toInt + d.toInt) / 4 := by
    rw [wavetables_shift_two, sum]
  rw [wavetables_keep16 _ (by omega) (by omega), quartered]
