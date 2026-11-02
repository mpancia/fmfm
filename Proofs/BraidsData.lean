import Firmware.Pitch
import Firmware.Percussion
import Firmware.NoiseSetup
import Firmware.VowelsSetup
import Firmware.WavetablesSetup

/-!
The facts about Braids' table data that the sample and setup proofs rest on, checked against the generated
copies in `Firmware/BraidsData.lean` (`make lint` keeps those in step with the C sources). Each check runs
the table's entries in the kernel; past the table every copy repeats its last entry, which closes the
unbounded statements.
-/

set_option maxRecDepth 4000

/-- Adding one to an index that is not at the top of the 32-bit range adds one to its value. -/
private theorem braids_data_succ_toNat (x : UInt32) (small : x.toNat < 4294967295) :
    (x + 1).toNat = x.toNat + 1 := by
  rw [UInt32.toNat_add]
  simp
  omega

/-- The phase step table's entries rise from one to the next, across the 97 entries. -/
private theorem braids_data_increments_rising_nat :
    ∀ i, i < 96 → BraidsData.oscillatorIncrement i ≤ BraidsData.oscillatorIncrement (i + 1) := by
  decide +kernel

/-- The phase step table's entries rise by less than 2^27 from one to the next, across the 97 entries. -/
private theorem braids_data_increments_close_nat :
    ∀ i, i < 96 → BraidsData.oscillatorIncrement (i + 1) - BraidsData.oscillatorIncrement i < 2 ^ 27 := by
  decide +kernel

/-- None of the phase step table's 97 entries passes the last one. -/
private theorem braids_data_increments_top_nat :
    ∀ i, i < 97 → BraidsData.oscillatorIncrement i ≤ 2588618730 := by
  decide +kernel

/-- Past the phase step table, the copy repeats its last entry. -/
private theorem braids_data_increments_tail (i : Nat) (past : 97 ≤ i) :
    BraidsData.oscillatorIncrement i = 2588618730 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 97 := ⟨i - 97, by omega⟩
  rfl

/-- No value of the phase step copy passes the last entry, at any index. -/
private theorem braids_data_increments_le (i : Nat) : BraidsData.oscillatorIncrement i ≤ 2588618730 := by
  by_cases inside : i < 97
  · exact braids_data_increments_top_nat i inside
  · have := braids_data_increments_tail i (by omega); omega

/-- The phase step accessor's value is the copy's, which fits 32 bits. -/
private theorem braids_data_increment_toNat (i : UInt32) :
    (Pitch.incrementTable i).toNat = BraidsData.oscillatorIncrement i.toNat := by
  unfold Pitch.incrementTable
  have := braids_data_increments_le i.toNat
  simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.reducePow]
  omega

/-- The phase step table rises from one entry to the next for every index the code reads (below 96:
`pitch_table_reads_inside`); the entry after the last is the copy's tail, so it is excluded.
Why it matters: `pitch_increment_bounded` blends two neighbouring entries and needs the second to be the
larger; this checks it against the data Braids ships. -/
theorem braids_data_increments_rising (i : UInt32) (inside : i.toNat < 96) :
    Pitch.incrementTable i ≤ Pitch.incrementTable (i + 1) := by
  rw [UInt32.le_iff_toNat_le, braids_data_increment_toNat, braids_data_increment_toNat,
    braids_data_succ_toNat _ (by omega)]
  exact braids_data_increments_rising_nat _ inside

/-- Two neighbouring phase step entries differ by less than 2^27 for every index the code reads (below 96).
Why it matters: the blend multiplies that difference by a 4-bit fraction in signed 32-bit arithmetic, and
2^27 * 15 is the most that fits. -/
theorem braids_data_increments_close (i : UInt32) (inside : i.toNat < 96) :
    (Pitch.incrementTable (i + 1)).toNat - (Pitch.incrementTable i).toNat < 2 ^ 27 := by
  rw [braids_data_increment_toNat, braids_data_increment_toNat, braids_data_succ_toNat _ (by omega)]
  exact braids_data_increments_close_nat _ inside

/-- No phase step entry passes 2588618730, the table's last, at any index.
Why it matters: the setup shifts the entry down at least one octave, and this top puts the result below
half a cycle (`pitch_increment_bounded`). -/
theorem braids_data_increments_top (i : UInt32) : (Pitch.incrementTable i).toNat ≤ 2588618730 := by
  rw [braids_data_increment_toNat]
  exact braids_data_increments_le _

/-- The cutoff table's entries rise from one to the next, across the 257 entries. -/
private theorem braids_data_cutoff_rising_nat :
    ∀ i, i < 256 → BraidsData.svfCutoff i ≤ BraidsData.svfCutoff (i + 1) := by
  decide +kernel

/-- None of the cutoff table's 257 entries passes the last one. -/
private theorem braids_data_cutoff_top_nat : ∀ i, i < 257 → BraidsData.svfCutoff i ≤ 25078 := by
  decide +kernel

/-- Past the cutoff table, the copy repeats its last entry. -/
private theorem braids_data_cutoff_tail (i : Nat) (past : 257 ≤ i) : BraidsData.svfCutoff i = 25078 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 257 := ⟨i - 257, by omega⟩
  rfl

/-- No value of the cutoff copy passes the last entry, at any index. -/
private theorem braids_data_cutoff_le (i : Nat) : BraidsData.svfCutoff i ≤ 25078 := by
  by_cases inside : i < 257
  · exact braids_data_cutoff_top_nat i inside
  · have := braids_data_cutoff_tail i (by omega); omega

/-- The cutoff accessor's value is the copy's, which fits 16 bits. -/
private theorem braids_data_cutoff_toNat (i : UInt32) :
    (Percussion.cutoffTable i).toNat = BraidsData.svfCutoff i.toNat := by
  unfold Percussion.cutoffTable
  have := braids_data_cutoff_le i.toNat
  simp only [Nat.toUInt16_eq, UInt16.toNat_ofNat', Nat.reducePow]
  omega

/-- The filter cutoff table rises from one entry to the next for every index a phase reads (below 256:
`tables_phase_reads_inside_257`).
Why it matters: `filters_setup_cutoff_in_range` blends two neighbouring entries and needs the second to be
the larger; this checks it against the data Braids ships. -/
theorem braids_data_cutoff_rising (i : UInt32) (inside : i.toNat < 256) :
    Percussion.cutoffTable i ≤ Percussion.cutoffTable (i + 1) := by
  rw [UInt16.le_iff_toNat_le, braids_data_cutoff_toNat, braids_data_cutoff_toNat,
    braids_data_succ_toNat _ (by omega)]
  exact braids_data_cutoff_rising_nat _ inside

/-- No filter cutoff entry passes 25078, the table's last, at any index.
Why it matters: the swarm's high-pass coefficient is a blend of two entries, so this is its range, which the
filters' sample theorems take. -/
theorem braids_data_cutoff_top (i : UInt32) : (Percussion.cutoffTable i).toNat ≤ 25078 := by
  rw [braids_data_cutoff_toNat]
  exact braids_data_cutoff_le _

/-- None of the grain envelope rate table's 257 entries passes 32768. -/
private theorem braids_data_rate_top_nat : ∀ i, i < 257 → BraidsData.granularEnvelopeRate i ≤ 32768 := by
  decide +kernel

/-- Past the rate table, the copy repeats its last entry. -/
private theorem braids_data_rate_tail (i : Nat) (past : 257 ≤ i) :
    BraidsData.granularEnvelopeRate i = 32768 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 257 := ⟨i - 257, by omega⟩
  rfl

/-- No grain envelope rate entry passes 32768, the table's last, at any index.
Why it matters: `noise_setup_grain_rate_bounded` shifts the entry up three places and needs the result below
2^18 to keep the grain's envelope reads inside their table. -/
theorem braids_data_rate_top (i : UInt32) : (NoiseSetup.rateTable i).toNat ≤ 32768 := by
  unfold NoiseSetup.rateTable
  have : BraidsData.granularEnvelopeRate i.toNat ≤ 32768 := by
    by_cases inside : i.toNat < 257
    · exact braids_data_rate_top_nat _ inside
    · have := braids_data_rate_tail i.toNat (by omega); omega
  simp only [Nat.toUInt16_eq, UInt16.toNat_ofNat', Nat.reducePow]
  omega

/-- Every amplitude of the 9 vowels' 3 formants is at most 15. -/
private theorem braids_data_vowel_amplitudes_nat :
    ∀ vowel, vowel < 9 → ∀ formant, formant < 3 → BraidsData.vowelAmplitude vowel formant ≤ 15 := by
  decide +kernel

/-- Past the formants of a vowel, the copy repeats its last entry. -/
private theorem braids_data_vowel_formant_tail (vowel k : Nat) (small : vowel < 9) :
    BraidsData.vowelAmplitude vowel (k + 3) = 14 := by
  have : vowel = 0 ∨ vowel = 1 ∨ vowel = 2 ∨ vowel = 3 ∨ vowel = 4 ∨ vowel = 5 ∨ vowel = 6 ∨ vowel = 7 ∨
    vowel = 8 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Past the vowels or the formants, the copy repeats its last entry. -/
private theorem braids_data_vowel_tail (vowel formant : Nat) (past : 9 ≤ vowel ∨ 3 ≤ formant) :
    BraidsData.vowelAmplitude vowel formant = 14 := by
  by_cases small : vowel < 9
  · obtain ⟨k, rfl⟩ : ∃ k, formant = k + 3 := ⟨formant - 3, by omega⟩
    exact braids_data_vowel_formant_tail vowel k small
  · obtain ⟨k, rfl⟩ : ∃ k, vowel = k + 9 := ⟨vowel - 9, by omega⟩
    rfl

/-- Every vowel formant amplitude is a nibble (at most 15), for any vowel and formant.
Why it matters: the formant tables are indexed by the phase's top nibble or-ed with the amplitude
(`tables_formant_reads_inside_256`); an amplitude above 15 would read past them. -/
theorem braids_data_vowel_amplitudes_are_nibbles (vowel formant : UInt32) :
    (VowelsSetup.vowelAmplitudeAt vowel formant).toNat ≤ 15 := by
  unfold VowelsSetup.vowelAmplitudeAt
  have : BraidsData.vowelAmplitude vowel.toNat formant.toNat ≤ 15 := by
    by_cases inside : vowel.toNat < 9 ∧ formant.toNat < 3
    · exact braids_data_vowel_amplitudes_nat _ inside.1 _ inside.2
    · have := braids_data_vowel_tail vowel.toNat formant.toNat (by omega); omega
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow]
  omega

/-- Every one of the 20 wavetable definitions has at most 16 steps. -/
private theorem braids_data_wavetable_steps_nat :
    ∀ table, table < 20 → BraidsData.wavetableSteps table ≤ 16 := by
  decide +kernel

/-- Past the 20 definitions, the copy repeats the last one's step count. -/
private theorem braids_data_wavetable_tail (table : Nat) (past : 20 ≤ table) :
    BraidsData.wavetableSteps table = 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, table = k + 20 := ⟨table - 20, by omega⟩
  rfl

/-- Every wavetable definition has at most 16 steps, for any table index.
Why it matters: `wavetables_setup_table_in_table` multiplies the parameter by the step count and needs the
pointer's step and the one after it inside the 17 steps of a definition; Braids ships 4, 8 or 16. -/
theorem braids_data_wavetable_steps_at_most_16 (table : UInt32) :
    (WavetablesSetup.tableSteps table).toNat ≤ 16 := by
  unfold WavetablesSetup.tableSteps
  have : BraidsData.wavetableSteps table.toNat ≤ 16 := by
    by_cases inside : table.toNat < 20
    · exact braids_data_wavetable_steps_nat _ inside
    · have := braids_data_wavetable_tail table.toNat (by omega); omega
  simp only [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.reducePow]
  omega
