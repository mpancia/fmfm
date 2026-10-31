import Firmware.Noise

/-- Between hits, a particle burst only fades: its amplitude after a sample is at most what it was.
Why it matters: particle noise dies away between hits; the burst cannot grow by itself. -/
theorem noise_particle_amplitude_fades (noise : UInt32) (amplitude : UInt16)
    (s1 c1 s2 c2 s3 c3 y11 y12 y21 y22 y31 y32 : Int32) :
    (Noise.particle noise amplitude s1 c1 s2 c2 s3 c3 y11 y12 y21 y22 y31 y32).amplitude ≤ amplitude := by
  unfold Noise.particle
  dsimp only
  rw [UInt16.le_iff_toNat_le, UInt32.toNat_toUInt16, UInt32.toNat_shiftRight, UInt32.toNat_mul,
    UInt16.toNat_toUInt32]
  have : (UInt32.toNat 16 % 32) = 16 := by decide
  rw [this, Nat.shiftRight_eq_div_pow]
  have := amplitude.toNat_lt
  have k : (64763 : UInt32).toNat = 64763 := by decide
  rw [k]
  have noWrap : amplitude.toNat * 64763 < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt noWrap]
  have : amplitude.toNat * 64763 / 2 ^ 16 ≤ amplitude.toNat := by omega
  rw [Nat.mod_eq_of_lt (by omega)]
  exact this
