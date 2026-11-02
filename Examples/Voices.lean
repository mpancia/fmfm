import Proofs.Pitch
import Proofs.Tables
import Proofs.BraidsData
import Proofs.Fm
import Proofs.FmLock
import Proofs.FmSymmetry
import Proofs.FmEnvelope
import Proofs.FmAlgorithms
import Proofs.FmDeviation
import Proofs.FmRange
import Proofs.Drum
import Proofs.Filter
import Proofs.Analog
import Proofs.Digital
import Proofs.Blend
import Proofs.Filters
import Proofs.Noise
import Proofs.Percussion
import Proofs.Physical
import Proofs.Vowels
import Proofs.Wavetables
import Proofs.VoiceSetup
import Proofs.Smooth
import Proofs.AnalogSetup
import Proofs.DigitalSetup
import Proofs.MacroSetup
import Proofs.FiltersSetup
import Proofs.NoiseSetup
import Proofs.PercussionSetup
import Proofs.PhysicalSetup
import Proofs.VowelsSetup
import Proofs.WavetablesSetup
import Proofs.Mix
import Proofs.Reverb
import Proofs.Delay

/-! Every public theorem about the voices and effects, applied to one concrete input with every
hypothesis discharged. Values are a middle C (note 60, pitch 60 * 128 = 7680), a half-open parameter
16000, 16-bit samples around ±1000, a full envelope 2^24 and a piano rate 960.

Theorems whose conclusion reads an `@[extern] opaque` table (sine, overdrive, wavetable bytes, formant
and physical-model tables) cannot have that conclusion evaluated by `decide`; the examples below still
instantiate their hypotheses on literals, which is all an application needs. They are marked `(opaque)`. -/

/-! Pitch -/

-- Middle C reads the increment table at an index and its successor both inside the 97 entries.
example := pitch_table_reads_inside 7680
-- Middle C's phase increment stays under Nyquist.
example := pitch_increment_bounded 7680

/-! Tables -/

-- A quarter-cycle phase reads the 257-entry tables inside.
example := tables_phase_reads_inside_257 0x40000000
-- A shape index of 30000 (under 65535) reads the shaper inside.
example := tables_shape_reads_inside_257 30000 (by decide)
-- A pitch of 8000 reads the resonator table inside 129 entries.
example := tables_resonator_reads_inside_129 8000
-- An arbitrary phase reads the 129-entry wave table inside.
example := tables_wave_reads_inside_129 0x12345678
-- A masked phase reads the wave line inside.
example := tables_wave_line_reads_inside_129 0x12345678 0xFFFF0000
-- A formant amplitude nibble of 9 keeps the formant index below 256.
example := tables_formant_reads_inside_256 0x12345678 9 (by decide)

/-! BraidsData -/

-- Increment entry 40 is no larger than entry 41.
example := braids_data_increments_rising 40 (by decide)
-- Entries 40 and 41 differ by less than 2^27.
example := braids_data_increments_close 40 (by decide)
-- Entry 40 is below the table top.
example := braids_data_increments_top 40
-- Cutoff entry 128 is no larger than entry 129.
example := braids_data_cutoff_rising 128 (by decide)
-- Cutoff entry 128 is at most 25078.
example := braids_data_cutoff_top 128
-- Grain rate entry 7 is at most 32768.
example := braids_data_rate_top 7
-- Vowel 2, formant 1 has a nibble amplitude.
example := braids_data_vowel_amplitudes_are_nibbles 2 1
-- Wavetable 5 has at most 16 steps.
example := braids_data_wavetable_steps_at_most_16 5

/-! Fm -/

-- The sine at an arbitrary phase fits 16 bits.
example := fm_sine_bounded 0x12345678
-- The sine is exact at the four quarter points.
example := fm_sine_exact_at_quarters
-- Quarter-wave entries 1000 and 1001 are within two of each other.
example := fm_sine_continuous 1000 (by decide)
-- An operator at the sine peak with a full envelope stays within 16 bits.
example := fm_operator_never_wraps 0x40000000 0 16777216 (by decide)
-- Carrying 20000 at half level never amplifies.
example := fm_carry_never_amplifies 20000 16384 (by decide) (by decide)
-- Saturating 40000 lands in range.
example := fm_saturate_in_range 40000
-- A full envelope at piano rate 960 falls, by at most a sixteenth.
example := fm_envelope_only_falls 16777216 960 (by decide) (by decide)
-- A voice increment times ratio 4.0 stays below Nyquist.
example := fm_increment_below_nyquist 0x02000000 1024
-- In algorithm 3, operator 2 is only modulated from above and operator 1 always carries.
example := fm_algorithms_well_founded 3 2 4
-- The piano shape (48) has ratios, levels and rates in range.
example := fm_shapes_in_range 48

/-! FmLock -/

-- A 3:1 ratio on a voice increment of 2^25 stays phase-locked after 7 samples.
example := fm_harmonic_ratios_lock 0x02000000 3 (by decide) (by decide) 7
-- ... and its sine is the sine of the tripled phase.
example := fm_integer_ratio_periodic 0x02000000 3 (by decide) (by decide) 7
-- Organ and bass use integer ratios; bell does not.
example := fm_organ_and_bass_lock

/-! FmSymmetry -/

-- Half a cycle later the sine is negated.
example := fm_sine_half_wave 0x12345678
-- The sine is mirror-symmetric about the quarter point.
example := fm_sine_quarter_wave 0x12345678
-- Opposite phases cancel exactly.
example := fm_sine_pairs_cancel 0x12345678
-- 256 evenly spaced samples from any start sum to zero.
example := fm_sine_has_no_dc 0x12345678

/-! FmEnvelope -/

-- A full envelope at rate 960 after 100 blocks is bounded and decays geometrically.
example := fm_envelope_after_bounded 16777216 960 (by decide) (by decide) 100
-- Rate 0 holds a full envelope for 5 blocks.
example := fm_held_envelope_holds 16777216 5
-- The shape tails land at the listed block counts.
example := fm_shape_tails

/-! FmAlgorithms -/

-- In algorithm 3, operator 3 carries or modulates something.
example := fm_no_operator_idle 3 2
-- All eight algorithms differ.
example := fm_algorithms_distinct
-- Shape 0 uses every operator.
example := fm_every_shape_uses_four_operators 0

/-! FmDeviation -/

-- The sine moves by at most 2 per 2^15 of phase between 1000 and 5000.
example := fm_sine_lipschitz 1000 5000 (by decide)
-- A modulator at increment 2^25 with a full envelope slews boundedly between samples 10 and 11.
example := fm_modulator_slew 0 0x02000000 16777216 (by decide) 10
-- Carrier at 2^24, modulator at 2^25, depth 4: the instantaneous deviation is bounded.
example := fm_carrier_frequency_deviation 0 0x01000000 0 0x02000000 16777216 4 (by decide) 10

/-! FmRange -/

-- The increment is the min of the product and the cap.
example := fm_cap_is_a_hold 0x02000000 1024
-- Below the cap the increment is the exact product.
example := fm_increment_exact_below_cap 0x02000000 1024 (by decide)
-- Middle C with the piano shape's operator-2 ratio never hits the cap.
example := fm_no_cap_on_the_keyboard 60 48 2 (by decide)

/-! Drum -/

-- The noise register has period 65535 from seed 1.
example := drum_noise_period
-- A live 16-bit seed never dies.
example := drum_noise_never_dies 0xACE1 (by decide) (by decide)
-- Noise from that seed fits 16 bits.
example := drum_noise_in_range 0xACE1
-- One pole from 1000 toward -2000 at half coefficient stays between them.
example := drum_one_pole_stays_between 1000 (-2000) 8192 (by decide) (by decide) (by decide)
-- A full drum envelope at rate 960 only falls.
example := drum_envelope_only_falls 16777216 960 (by decide) (by decide)
-- A sweep from 2^27 down to 2^25 at rate 4000 lands between them.
example := drum_sweep_lands 0x08000000 0x02000000 4000 (by decide) (by decide)
-- A sweep start for target 2^25 and colour 16000 is below Nyquist.
example := drum_sweep_start_below_nyquist 0x02000000 16000
-- Six metal phases sum inside 16 bits.
example := drum_metal_sum_fits 0x10000000 0x20000000 0x30000000 0x40000000 0x50000000 0x60000000
-- A square at any phase is at most 5461.
example := drum_square_in_range 0x12345678
-- A full envelope at level 20000 gains at most 20000.
example := drum_gain_never_amplifies 16777216 20000 (by decide) (by decide)
-- The metal chain from states 1000 and 2000 with half coefficients and gain 16000 stays bounded.
example := drum_metal_chain_bounded 0x10000000 0x20000000 0x30000000 0x40000000 0x50000000 0x60000000
  1000 2000 8192 4096 16000 (by decide) (by decide) (by decide) (by decide) (by decide)
-- Every drum output from small states and half coefficients stays inside the master's limit.
example := drum_output_never_wraps 0x10000000 0x20000000 0x30000000 0x40000000 0x50000000 0x60000000
  0xACE1 1000 2000 (-1000) (-2000) 8192 4096 2048 1024 16000 12000
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide) (by decide)
-- Shape 0 at timbre 16000, colour 20000 has rates, levels and coefficients in range.
example := drum_shapes_in_range 0 16000 20000
-- The drum tails land at the listed block counts.
example := drum_tails

/-! Filter -/

-- Cutoff 100, resonance 0 is off and passes states 100, 200 and sample 3000 unchanged.
example := filter_open_is_identity 0 100 200 3000
-- States ±200, sample 3000 with mid coefficients stay bounded through every stage.
example := filter_states_stay_bounded 100 (-200) 3000 16000 20000 10000 5000 0
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
-- Cutoff 50, resonance 30 give coefficients in range.
example := filter_coefficients_in_range 50 30 16000 8000 (by decide)
-- A settled filter at cutoff 50, resonance 30 holds DC 3000 in every mode.
example := filter_settled_dc_holds 50 30 2 3000 (by decide) (by decide)
-- Lowpass from 1000 toward 3000 steps toward the input.
example := filter_lowpass_steps_toward_input 1000 3000 16000 20000 10000
  (by decide) (by decide) (by decide) (by decide)

/-! Analog -/

-- This-sample BLEP is nonnegative and at most 16383.
example := analog_this_blep_range 0x12345678
-- Next-sample BLEP is nonpositive and at least -16383.
example := analog_next_blep_range 0x12345678
-- A triangle half is within ±16384.
example := analog_triangle_half_range 0x12345678
-- A triangle at increment 2^25 without sync is the sum of its two halves.
example := analog_triangle_never_wraps 0x12345678 0x02000000 0
-- The interpolated sine lies between its table neighbours (opaque).
example := analog_sine_between_entries 0x12345678
-- After 100 samples at increment 2^25 the phase is exact modulo 2^32.
example := analog_phase_exact 0x12345678 0x02000000 100

/-! Digital -/

-- Mixing 1000 and -2000 at balance 30000 lands between them.
example := digital_mix_between_inputs 1000 (-2000) 30000 (by decide) (by decide) (by decide)
-- Clipping 40000 fits 16 bits.
example := digital_clip_never_wraps 40000
-- The three FM shapes are the stated sine reads (opaque).
example := digital_fm_never_wraps 0x10000000 0x20000000 0x01000000 0x00800000 100 5000 20000 0
-- The ring product of 1000 and -2000 is exact and within ±16384.
example := digital_ring_product_never_wraps 1000 (-2000) (by decide) (by decide)
-- Ring modulation is the stated overdriven product (opaque).
example := digital_ring_mod_never_wraps 0x10000000 0x20000000 0x30000000 0x01000000 0x00800000 0x00400000 0
-- The toy filter on bytes 10, 20, 30, 40 is the stated weighted sum.
example := digital_toy_never_wraps 10 20 30 40

/-! Blend -/

-- An 8.8 blend of 1000 and -2000 lies between them.
example := blend_eight_between 1000 (-2000) 0x12345678 (by decide) (by decide)
-- A 16.16 blend of 1000 and -2000 lies between them.
example := blend_sixteen_between 1000 (-2000) 0x12345678 (by decide) (by decide)

/-! Filters -/

-- Seven swarm phases sum within the stated range.
example := filters_swarm_sum_range 0x10000000 0x20000000 0x30000000 0x40000000 0x50000000 0x60000000
  0x70000000
-- A harmonic glide from 1000 toward 2000 approaches without overshoot.
example := filters_harmonic_glide_approaches 1000 2000 (by decide) (by decide) (by decide)
-- The swarm filter output is the stated clipped expression.
example := filters_swarm_filter_never_wraps 3000 16000 8000 1000 2000
-- A windowed carrier 1000 under window 40000 in filter type 2 is exact.
example := filters_windowed_carrier_never_wraps 1000 40000 2 (by decide) (by decide)
-- VOSIM output is the stated bell-shaped product (opaque).
example := filters_vosim_never_wraps 0x10000000 0x01000000 0x20000000 0x30000000 0x00800000 0x00400000 0
-- Harmonics sum 40000 clips and averages with the previous 1000.
example := filters_harmonics_never_wraps 40000 1000 (by decide)

/-! Noise -/

-- A particle's amplitude never grows past 30000 (opaque).
example := noise_particle_amplitude_fades 0x12345678 30000 30000 (-20000) 30000 (-20000) 30000 (-20000)
  500 (-500) 500 (-500) 500 (-500)
-- Overdrive index of 1000 is inside the table.
example := noise_overdrive_index_in_table 1000 (by decide)
-- Correcting 40000 at gain 16000 clips then scales.
example := noise_corrected_never_wraps 40000 16000 (by decide)
-- Boosting 40000 by makeup 4000 saturates to 32767.
example := noise_boost_never_wraps 40000 4000 (by decide) (by decide)
-- A resonator on input 1000 with bounded coefficients and states is the stated clipped sum.
example := noise_resonate_never_wraps 1000 30000 (-20000) 32506 500 (-500)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
-- A burst scales the noise word by its amplitude.
example := noise_burst_never_wraps 0x12345678 30000
-- A particle output is the clipped sum of three resonators (opaque).
example := noise_particle_never_wraps 0x12345678 30000 30000 (-20000) 30000 (-20000) 30000 (-20000)
  500 (-500) 500 (-500) 500 (-500)
-- A cloud sum of 40000 is clipped.
example := noise_cloud_out_never_wraps 40000
-- A grain contributes a sine scaled by its envelope, within ±16384 (opaque).
example := noise_grain_never_wraps 0x10000000 0x01000000 16777216 1000
-- A grain envelope at 2^24 advancing by 1000 reads inside the table.
example := noise_grain_envelope_index_in_table 0x10000000 0x01000000 16777216 1000 (by decide) (by decide)

/-! Percussion -/

-- An excitation of 10000 with decay 2000 and counter 0 decays.
example := percussion_excite_decays 10000 2000 0 100 (by decide) (by decide) (by decide) (by decide)
-- Amplitude 20000 under decays 40000/20000 and parameter 16000 never grows.
example := percussion_decay_never_grows 20000 40000 20000 16000 (by decide) (by decide) (by decide)
-- A bell partial at amplitude 20000 is the stated sine product (opaque).
example := percussion_bell_partial_never_wraps 0x10000000 0x01000000 20000 (by decide)
-- A drum partial fading from 20000 to 10000 at half fade is the stated product (opaque).
example := percussion_drum_partial_never_wraps 0x10000000 0x01000000 20000 10000 16384
  (by decide) (by decide) (by decide)
-- The snare mix with gains 16000/20000 is the stated clipped sum.
example := percussion_snare_never_wraps 1000 100000 (-2000) 50000 500 16000 20000
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
-- Crossfading metal 1000 to white -2000 at 16000 is the stated interpolation.
example := percussion_cymbal_never_wraps 1000 (-2000) 16000 (by decide)
-- Drum noise states ±4000 under coefficient 16000 stay within ±16384.
example := percussion_drum_noise_stays_bounded 1000 2000 (-3000) 4000 16000
  (by decide) (by decide) (by decide) (by decide)
-- The drum mix of bounded partials is the stated clipped sum.
example := percussion_drum_mix_never_wraps 20000 1000 2000 10000 8000 6000 8000
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! Physical -/

-- Mixing 1000 and -2000 at fraction 30000 is exact.
example := physical_mix_never_wraps 1000 (-2000) 30000 (by decide) (by decide) (by decide)
-- A comb on input 1000 between taps 2000 and -3000 is the stated clipped pair.
example := physical_comb_never_wraps 1000 2000 (-3000) 30000 20000
  (by decide) (by decide) (by decide) (by decide) (by decide)
-- The comb resonance index of 1000 is inside the table.
example := physical_comb_resonance_index_in_table 1000
-- Filling a pluck line from 1000 with noise -2000 is exact.
example := physical_pluck_fill_never_wraps 1000 (-2000) (by decide) (by decide)
-- Averaging 1000 and -2000 at loss 16000 gains nothing.
example := physical_pluck_average_no_gain 1000 (-2000) 16000 (by decide) (by decide) (by decide)
-- Reading between 1000 and -2000 at a phase is exact.
example := physical_pluck_read_never_wraps 1000 (-2000) 0x12345678 (by decide) (by decide)
-- Half-rate output of sum 40000 with previous 1000 is the clipped average.
example := physical_half_rate_never_wraps 40000 1000 (by decide)
-- The bowed string output from byte-sized bridge taps and small body states is the stated clip.
example := physical_bowed_never_wraps 100 (-50) 10 20 30000 40000 500 100 200 1000 (-2000)
  (by decide) (by decide) (by decide) (by decide) (by decide)
-- Its lowpass state from 500 stays within ±32768.
example := physical_bowed_lowpass_stays_bounded 100 (-50) 10 20 30000 40000 500 100 200 1000 (-2000)
  (by decide) (by decide) (by decide) (by decide)
-- The friction index for delta 1000, bow 500 is inside the table.
example := physical_friction_index_in_table 1000 500 (by decide)
-- The blown filter state from 200 at coefficient 2048 stays between bore and old state (opaque).
example := physical_blown_filter_stays_between 1000 2000 3000 30000 500 100 200 2048 (by decide) (by decide)
-- The flute output from byte-sized bore taps is the stated clip (opaque).
example := physical_fluted_never_wraps 100 (-50) 10 20 30000 40000 500 1000 2000 3000 4000 5000 6000
  (by decide) (by decide) (by decide)
-- The jet index of 1000 is inside the table.
example := physical_jet_index_in_table 1000
-- The bowed body biquad state stays within 2^18.
example := physical_bowed_body_stays_bounded 100 (-50) 10 20 30000 40000 500 100 200 1000 (-2000)
-- Comb read at ptr 100, integral 200 is inside the 8192 line.
example := physical_comb_read_in_line 100 200
-- Comb write after ptr 100 is inside the line.
example := physical_comb_write_in_line 100
-- A pluck line oversampled by shift 2 (size 256) reads inside.
example := physical_pluck_read_in_line 0x12345678 2 256 rfl (by decide)
-- Its read and next-write pointers are inside.
example := physical_pluck_next_in_line 0x12345678 2 255 256 100 rfl rfl (by decide)
-- Filling entry 100 of 256 is inside.
example := physical_pluck_fill_in_line 100 256 (by decide) (by decide)
-- Bowed bridge and neck lines at ptr 100 read and write inside.
example := physical_bowed_lines_in_line 100 200 300
-- The blown bore at ptr 100 reads and writes inside.
example := physical_blown_bore_in_line 100 200
-- The flute bore and jet lines at ptr 100 read and write inside.
example := physical_fluted_lines_in_line 100 200 300

/-! Vowels -/

-- A FOF filter at amplitude 20000 contributes within ±8192.
example := vowels_fof_contribution_never_wraps 1000 2000 3000 20000 500 (by decide)
-- FOF output of sum 40000 with previous 1000 clips and averages.
example := vowels_fof_out_never_wraps 40000 1000 (by decide)
-- Question drive on sample 20000 at parameter 16000 is nonnegative and within 65535.
example := vowels_question_drive_never_wraps 20000 16000 (by decide) (by decide)

/-! Wavetables -/

-- A wavetable step at increment 2^25 is the average of two crossfades (opaque).
example := wavetables_wavetable_never_wraps 0x10000000 0x02000000 3 4 30000 0
-- A crossfade of waves 3 and 4 lies between their reads (opaque).
example := wavetables_crossfade_between_waves 3 4 0x12345678 30000
-- A wave read lies between its neighbouring bytes (opaque).
example := wavetables_read_between_bytes 3 0x12345678
-- A wave map step sums two map reads (opaque).
example := wavetables_wave_map_never_wraps 0x10000000 0x02000000 1 2 3 4 30000 40000 0
-- A wave line step averages two line pairs (opaque).
example := wavetables_wave_line_never_wraps 0x10000000 0x02000000 1 2 30000 100 0xFF 3 4 40000 200 0xFF
  30000 0
-- A paraphonic step averages four crossfades (opaque).
example := wavetables_paraphonic_never_wraps 0x10000000 0x20000000 0x30000000 0x40000000 0x01000000
  0x01400000 0x01800000 0x01C00000 3 4 30000

/-! VoiceSetup -/

-- Middle C with timbre 16000 sets pitch 7680 under the table start and parameter 16000.
example := voice_setup_pitch_in_range 60 (by decide) 16000 (by decide) (by decide)
-- Shape 5 maps inside the 48 shapes.
example := voice_setup_shape_in_table 5

/-! Smooth -/

-- Smoothing from 1000 toward 20000 at crossfade 16000 lies between.
example := smooth_parameter_between 1000 20000 16000 (by decide) (by decide) (by decide)
-- After a block of 64 the parameter is within 64 of 20000.
example := smooth_parameter_reaches_target 1000 20000 64 (by decide) (by decide) (by decide) (by decide)
-- Step 10 of a 64-step glide from 1000 to 5000 stays within the glide.
example := smooth_step_glide_bound 1000 5000 64 (by decide) 10 (by decide)
-- Step 64 lands within 64 of 5000.
example := smooth_step_lands_near_target 1000 5000 64 (by decide) (by decide)

/-! AnalogSetup -/

-- Parameter 16000 gives pulse widths in range.
example := analog_setup_pulse_width_in_range 16000 (by decide)
-- Middle C with parameter 16000 picks buzz zones inside the table.
example := analog_setup_buzz_zone_in_table 7680 16000

/-! DigitalSetup -/

-- The FM quantizer index for parameter 16000 is inside the table.
example := digital_setup_fm_quantizer_in_table 16000 (by decide)
-- Middle C with parameter 16000 gives modulator increments below Nyquist.
example := digital_setup_increments_half_cycle 7680 16000 0x02000000
-- Middle C's delay index is inside the table.
example := digital_setup_delay_in_table 7680

/-! MacroSetup -/

-- Middle C with parameter 16000 gives macro parameters in range.
example := macro_setup_parameters_in_range 7680 16000 (by decide)
-- Its morph cutoff reads inside the table.
example := macro_setup_cutoff_in_table 7680 16000
-- Parameter 16000 picks triple intervals inside the table.
example := macro_setup_triple_intervals_in_table 16000 (by decide)

/-! FiltersSetup -/

-- Middle C with parameter 16000 reads the swarm highpass cutoff inside the table.
example := filters_setup_cutoff_in_table 7680 16000
-- Blending the rising cutoff table (top 25078) never exceeds its top.
example := filters_setup_table_blend_le_top Percussion.cutoffTable 0x12345678 25078
  (fun i h => braids_data_cutoff_rising i h) braids_data_cutoff_top (by decide)
-- The swarm cutoff for middle C is within 0..25078.
example := filters_setup_cutoff_in_range 7680 16000

/-! NoiseSetup -/

-- Middle C and parameter 16000 read the cutoff table inside.
example := noise_setup_cutoff_in_table 7680 16000
-- Their gain correction is in range.
example := noise_setup_gain_correction_in_range 7680 16000
-- Parameter 16000 reads the grain rate table inside.
example := noise_setup_grain_rate_in_table 16000 (by decide)
-- Its grain rate is at most 2^18.
example := noise_setup_grain_rate_bounded 16000
-- Resetting a grain from envelope 2^24 at rate 1000 stays inside the table.
example := noise_setup_grain_reset 16777216 1000 0x12345678 16000 (by decide) (by decide)
-- The quantizer divider for 16000 is a positive period.
example := noise_setup_clock_period_positive 16000 (by decide)

/-! PercussionSetup -/

-- Partial 3's decays are ordered and in range.
example := percussion_setup_partial_decay_in_table 3
-- Partial 3's amplitudes are in range.
example := percussion_setup_amplitudes_in_range 3
-- Middle C with parameter 16000 reads the drum cutoff inside the table.
example := percussion_setup_drum_cutoff_in_table 7680 16000
-- Parameters 16000 and 20000 give gains in range.
example := percussion_setup_gains_in_range 16000 20000 (by decide) (by decide)

/-! PhysicalSetup -/

-- Increment 2^25 with parameter 16000 gives a valid pluck line size.
example := physical_setup_pluck_size_valid 0x02000000 16000 (by decide)
-- Comb delay 1000 is inside the line.
example := physical_setup_comb_delay_in_line 1000
-- Advancing the excitation pointer 100 by 8 stays inside the tables.
example := physical_setup_envelope_pointer_in_table 100 8 (by decide)
-- Middle C with parameter 16000 picks flute bodies inside the table.
example := physical_setup_flute_body_in_table 7680 16000

/-! VowelsSetup -/

-- Parameter 16000 picks a vowel inside the table.
example := vowels_setup_vowel_index_in_table 16000 (by decide)
-- Random word 12345 picks a consonant inside the table.
example := vowels_setup_consonant_index_in_table 12345
-- Parameter 16000 picks a FOF row inside the table.
example := vowels_setup_fof_reads_in_table 16000 (by decide)
-- Formant 1 at parameter 16000 has a nibble amplitude (opaque).
example := vowels_setup_formant_amplitude_in_range 16000 1
-- The FOF amplitude of formant 1 fits 16 bits (opaque).
example := vowels_setup_fof_amplitude_16bit 16000 20000 1

/-! WavetablesSetup -/

-- Parameters 16000 and 8000 pick a table and step inside.
example := wavetables_setup_table_in_table 16000 8000 (by decide) (by decide)
-- Corner (1, 0) of the map at those parameters is inside.
example := wavetables_setup_map_in_table 16000 8000 1 0 (by decide) (by decide) (by decide) (by decide)
-- A line scan from 30000 reads inside and stays settled.
example := wavetables_setup_line_in_table 30000 8000 16000 (by decide) (by decide) (by decide)
-- Paraphonic chord and wave indices are inside.
example := wavetables_setup_paraphonic_in_table 16000 8000 (by decide) (by decide)
-- Wave 100 at any phase reads inside the bank.
example := wavetables_setup_wave_in_bank 100 0x12345678 (by decide)
-- Voice 2 of middle C with parameter 16000 has an increment below Nyquist.
example := wavetables_setup_increments_half_cycle 7680 16000 2

/-! Mix -/

-- An envelope at 50000 rising toward 130048 by 512 stays between and in range.
example := mix_envelope_toward_gate 50000 130048 512 100 (by decide) (by decide) (by decide) (by decide)
-- Sample -20000 at gain 1024, send 128, half amplitude never wraps.
example := mix_voice_sample_never_wraps (-20000) 1024 128 65536 (by decide) (by decide) (by decide)
-- Three voices plus a wet return at unity never wrap.
example := mix_bus_never_wraps [1000, -2000, 3000] 100000 32768
  (by decide) (by decide) (by decide) (by decide)
-- Limiting 600000 fits the master.
example := mix_limit_fits_master 600000
-- Mixing wet 100000 at unity into 100000 is exact and held.
example := mix_in_never_wraps 100000 100000 32768 (by decide) (by decide) (by decide)
-- The machine sample from three voices, echo 20000 and wet 100000 stays bounded.
example := mix_machine_sample_bounded [1000, -2000, 3000] 20000 32768 100000 32768
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
-- Centre pan is equal-power.
example := mix_pan_equal_power 0x40000000
-- Panning 50000 at half gain never amplifies.
example := mix_pan_never_amplifies 50000 16384 (by decide) (by decide) (by decide)

/-! Reverb -/

-- Write 100, base 200, offset 300 stays in the ring.
example := reverb_position_in_ring 100 200 300
-- At scale 300 line 4 fits and abuts line 5.
example := reverb_lines_fit_and_do_not_overlap 300 (by decide) 4 (by decide)
-- Setting 60 gives time and brightness gains below one.
example := reverb_gains_below_one 60
-- Compressing 300000 saturates.
example := reverb_compress_saturates 300000
-- Multiplying 100000 by half gain never amplifies.
example := reverb_gain_never_amplifies 100000 16384 (by decide) (by decide) (by decide)
-- Lowpass from 1000 toward -2000 at half stays between.
example := reverb_lowpass_stays_between 1000 (-2000) 16384 (by decide) (by decide) (by decide) (by decide)
-- Interpolating 1000 and -2000 at fraction 30000 stays between.
example := reverb_interpolation_stays_between 1000 (-2000) 30000
  (by decide) (by decide) (by decide) (by decide)
-- The LFO at any phase is in 0..32767.
example := reverb_lfo_in_range 0x12345678
-- At scale 300 with LFO 20000 the modulated reads stay in their lines.
example := reverb_modulated_read_stays_in_line 300 20000 (by decide) (by decide) (by decide)
-- A tail of 100000 at decay 30000 decays over a round trip.
example := reverb_round_trip_decays 100000 30000 16384 20000
  (by decide : (100000 : Int32).toInt.natAbs ≤ 262144) (by decide) (by decide) (by decide) (by decide)
-- The wet path from send 2^20 and small stored samples never overflows.
example := reverb_wet_never_overflows 1048576 20000 20000 30000 16384 1000000 32768
  1000 (-2000) 3000 (-4000) 100000 5000 (-6000)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  (by decide : (1000 : Int32).toInt.natAbs ≤ 262144) (by decide : (-2000 : Int32).toInt.natAbs ≤ 262144)
  (by decide : (3000 : Int32).toInt.natAbs ≤ 262144) (by decide : (-4000 : Int32).toInt.natAbs ≤ 262144)
  (by decide : (100000 : Int32).toInt.natAbs ≤ 262144) (by decide : (5000 : Int32).toInt.natAbs ≤ 262144)
  (by decide : (-6000 : Int32).toInt.natAbs ≤ 262144)
-- A tail of 100000 stays in memory for 5 trips.
example := reverb_tail_stays_in_memory 100000 30000 16384 20000
  (by decide : (100000 : Int32).toInt.natAbs ≤ 262144) 5
-- A tail of 100000 at decay 30000 dies away over 5 trips.
example := reverb_tail_dies_away 100000 30000 16384 20000
  (by decide : (100000 : Int32).toInt.natAbs ≤ 262144) (by decide) (by decide) (by decide) (by decide) 5

/-! Delay -/

-- Setting 60 gives feedback and tone gains in range.
example := delay_gains_in_range 60
-- An echo of 20000 at feedback 30000 shrinks by a twentieth.
example := delay_echo_shrinks 20000 30000 (by decide) (by decide) (by decide)
-- Time 3 at 120 bpm, 44100 Hz fits the line.
example := delay_samples_in_line 3 120 44100
-- Write 100, offset 200 stay in the line.
example := delay_position_in_line 100 200 (by decide) (by decide)
-- Time 3 at 120 bpm is the exact note length in samples.
example := delay_notes_exact 3 120 (by decide) (by decide) (by decide)
-- Storing 40000 saturates.
example := delay_store_saturates 40000
-- Ten hops of a 20000 echo at feedback 30000 die away geometrically.
example := delay_echoes_die_away 20000 30000 (by decide) (by decide) (by decide) 10

/-! Rejections: the spec says no to bad behaviour -/

-- `Fm.saturate` holds 40000 to 32767 rather than letting it through.
#guard Fm.saturate 40000 = 32767
#guard Fm.saturate 40000 ≠ 40000
-- A product past Nyquist is capped at 2^31 instead of wrapping (the 32-bit product would be 0).
#guard Fm.increment 0x80000000 4096 = 2147483648
#guard (0x80000000 : UInt32) * 4096 / 256 = 0
-- An FM envelope step never rises: from 2^24 at rate 960 it goes down, and it never goes up.
#guard Fm.envelopeStep 16777216 960 < 16777216
#guard !(Fm.envelopeStep 16777216 960 > 16777216)
-- With cutoff 50 the filter is active and is not the identity on a nonzero state ...
#guard Filter.active 50 0 = true
#guard (Filter.step 50 0 0 1000 1000 0).out ≠ 0
#guard (Filter.step 50 0 0 1000 1000 0).ic1 ≠ 1000
-- ... while with cutoff 100 and resonance 0 it is off and passes everything through.
#guard Filter.active 100 0 = false
#guard (Filter.step 100 0 0 1000 1000 0).out = 0 && (Filter.step 100 0 0 1000 1000 0).ic1 == 1000
-- The noise register from seed 0 stays 0: a dead seed, which is why `drum_noise_never_dies` needs `s ≠ 0`.
#guard Drum.lfsr 0 = 0
example : ¬ (Drum.lfsr 0 ≠ 0) := by decide
-- A one-pole output never leaves its inputs: from 1000 toward -2000 at half it lands at -500.
#guard Drum.onePole 1000 (-2000) 8192 = -500
#guard !(Drum.onePole 1000 (-2000) 8192 > 1000 || Drum.onePole 1000 (-2000) 8192 < -2000)
-- `Mix.limit` holds a value past the limit.
#guard Mix.limit 600000 = 524287
#guard Mix.limit (-600000) = -524287
-- A delay feedback setting past 100 is clipped to the gain at 100; a sample past 16 bits is stored clipped.
#guard Delay.feedbackGain 250 = Delay.feedbackGain 100
#guard Delay.store 40000 = 32767
-- A reverb time setting past 100 is clipped to the gain at 100, and a signal past the compressor saturates.
#guard Reverb.timeGain 500 = Reverb.timeGain 100
#guard Reverb.compress 300000 = 32767
