import Firmware.Digital
import Firmware.Random

set_option compiler.extract_closed false

/-!
# Delay-line engines, one sample at a time

Port of the comb filter, plucked string, bowed string, blown pipe and flute engines of Braids
(`digital_oscillator.cc`, Emilie Gillet, MIT). The delay lines live in the C++ oscillator. `voices/physical_glue.c`
owns them, does every load, store and pointer wrap, and hands this file the values it read; each function here
returns the values to store. The random numbers come from C too. Same shape as `Firmware/Digital.lean`: pure scalar functions, one result structure per
engine, each field exported on its own by `Firmware/PhysicalApi.lean`. Lean shifts bind tighter than `*` and `+`,
so shifted products are parenthesized.
-/

/-- One entry of Braids' bowing envelope (`lut_bowing_envelope`), looked up by C. Trusted data. -/
@[extern "fm1_braids_lut_bowing_envelope"] opaque Physical.bowingEnvelope (index : UInt32) : UInt16

/-- One entry of Braids' bowing friction curve (`lut_bowing_friction`, 256 entries), looked up by C. Trusted data. -/
@[extern "fm1_braids_lut_bowing_friction"] opaque Physical.bowingFriction (index : UInt32) : UInt16

/-- One entry of Braids' blowing envelope (`lut_blowing_envelope`), looked up by C. Trusted data. -/
@[extern "fm1_braids_lut_blowing_envelope"] opaque Physical.blowingEnvelope (index : UInt32) : UInt16

/-- One entry of Braids' flute jet curve (`lut_blowing_jet`, 256 entries), looked up by C. Trusted data. -/
@[extern "fm1_braids_lut_blowing_jet"] opaque Physical.blowingJet (index : UInt32) : Int16

/-- Blend two delay-line samples by a 16-bit fraction (Braids' `Mix`). The blend of two 16-bit values stays in 16
bits, so no truncation is needed. -/
@[inline] def Physical.mix (a b : Int32) (fraction : UInt32) : Int32 :=
  (a * ((65535 : Int32) - fraction.toInt32) + b * fraction.toInt32) >>> 16

/-- Half the sum of two samples, cut to 16 bits: the in-between sample when an engine runs at half rate. -/
@[inline] def Physical.halfSum (a b : Int32) : Int16 := ((a + b) >>> 1).toInt16

/-- The result of one comb filter sample: the sample written into the delay line and the output. -/
structure CombStep where
  feedback : Int16
  out : Int16

/-- Comb filter: the input plus the delay line's sample from `delay` ago, which is blended between two neighbours
by `fraction` (0 to 65535). `resonance` (-32768 to 32767) scales what is fed back into the line. -/
@[inline] def Physical.comb (input a b fraction resonance : Int32) : CombStep :=
  let delayed := a + (((b - a) * (fraction >>> 1)) >>> 15)
  let feedback := Digital.clip (((delayed * resonance) >>> 15) + (input >>> 1))
  let out := Digital.clip ((input + (delayed <<< 1)) >>> 1)
  { feedback := feedback.toInt16, out := out.toInt16 }

/-- Where the comb filter's resonance setting (0 to 32767) falls on the overdrive curve: the setting spread over
the curve's 16-bit range. -/
@[inline] def Physical.combResonanceIndex (parameter : Int32) : UInt32 :=
  (((parameter <<< 1) - 32768).toInt16.toInt32 + 32768).toUInt32

/-- The comb filter's resonance setting (0 to 32767) bent by Braids' overdrive curve, so the extremes can be set
more finely (`Interpolate88` over `ws_moderate_overdrive`). -/
@[inline] def Physical.combResonance (parameter : Int32) : Int32 :=
  Analog.shape Digital.overdriveTable (Physical.combResonanceIndex parameter)

/-- Plucked string: the value that fills one place of a new string's delay line. It is the old content with white
noise mixed in (three quarters noise). -/
@[inline] def Physical.pluckFill (old noise : Int32) : Int16 := ((old + 3 * noise) >>> 2).toInt16

/-- Plucked string: is this place of the delay line averaged this time? `word` is a random number, `probability`
the chance (0 to 65535, a bit more means always). -/
@[inline] def Physical.pluckUpdates (word probability : UInt32) : UInt8 :=
  if (word &&& 0xFFFF) ≤ probability then 1 else 0

/-- Plucked string: the low-pass step of the Karplus-Strong loop. The mean of two neighbours (rounded toward
zero), made quieter by `loss` (0 to 4096) when it is not zero. -/
@[inline] def Physical.pluckAverage (a b loss : Int32) : Int16 :=
  let s := a + b
  let half := if s < 0 then -((-s) >>> 1) else s >>> 1
  (if loss != 0 then (half * ((32768 : Int32) - loss)) >>> 15 else half).toInt16

/-- Plucked string: the delay line read at a 32-bit phase of which the top 10 bits pick the entry, blended with the
next one (Braids' `Interpolate1022`). -/
@[inline] def Physical.pluckRead (a b : Int32) (phase : UInt32) : Int32 :=
  (a + (((b - a) * ((phase >>> 6) &&& 0xFFFF).toInt32) >>> 16)).toInt16.toInt32

/-- The result of one bowed string sample: the loop's low-pass state, the two samples written into the delay
lines, the biquad's new output state and the sample. -/
structure BowedStep where
  lp : Int32
  neck : UInt8
  bridge : UInt8
  biquad : Int32
  out : Int16

/-- Bowed string: where the bow's speed against the string (`delta`, pressed with `bow`) falls on the 257-entry
friction curve. The size of the product is capped at 131071 before its top 8 bits pick the entry. -/
@[inline] def Physical.frictionIndex (delta bow : Int32) : UInt32 :=
  let raw := (delta * bow) >>> 5
  let magnitude := if raw < 0 then -raw else raw
  let capped := if magnitude >= 131072 then 131071 else magnitude
  (capped >>> 9).toUInt32

/-- Bowed string: a digital waveguide. The string is two delay lines (bridge side and neck side) with a bow that
pushes the velocity toward its own through a friction curve; a low-pass at the bridge and a biquad stand in for the
body. `excitation` walks the bowing envelope, `bow` (about 45 to 172) is the bow pressure, `y0` and `y1` are the
biquad's last two outputs. The delay-line samples are 8 bits, so the stores are cut to 8. -/
@[inline] def Physical.bowed (bridgeA bridgeB nutA nutB : Int32) (bridgeFraction neckFraction : UInt32)
    (lp : Int32) (excitation : UInt32) (bow : Int32) (y0 y1 : Int32) : BowedStep :=
  let bridgeValue := Physical.mix bridgeA bridgeB bridgeFraction <<< 8
  let nutValue := Physical.mix nutA nutB neckFraction <<< 8
  let lp' := ((bridgeValue * 14008) + (lp * 18022)) >>> 15
  let bridgeReflection := -lp'
  let nutReflection := -nutValue
  let stringVelocity := bridgeReflection + nutReflection
  let envelope := (Physical.bowingEnvelope (excitation >>> 1)).toUInt32.toInt32
      + (Physical.bowingEnvelope ((excitation + 1) >>> 1)).toUInt32.toInt32
  let bowVelocity := envelope >>> 1
  let delta := bowVelocity - stringVelocity
  let friction := (Physical.bowingFriction (Physical.frictionIndex delta bow)).toUInt32.toInt32
  let velocity := (friction * delta) >>> 15
  let temp := ((bridgeValue * 6553) >>> 15) + ((y0 * 6948) >>> 12) + ((y1 * (-2959 : Int32)) >>> 12)
  let out := Digital.clip (temp - y1)
  { lp := lp', neck := ((bridgeReflection + velocity) >>> 8).toUInt32.toUInt8,
    bridge := ((nutReflection + velocity) >>> 8).toUInt32.toUInt8, biquad := temp, out := out.toInt16 }

/-- The result of one blown pipe sample: the low-pass state, the sample written into the bore, and the output
filter's state (which is also the output). -/
structure BlownStep where
  lp : Int32
  bore : Int16
  filter : Int16

/-- Blown pipe: a bore delay line with a reed at its end. Breath pressure is noise (`parameter`, up to 28000, sets
how much) on a steady pressure; the reed turns the pressure difference across it into the bore's next sample. A
one-pole low-pass with coefficient `coefficient` (out of 4096) models the body and gives the output. -/
@[inline] def Physical.blown (noise a b : Int32) (fraction : UInt32) (lp parameter filter coefficient : Int32) :
    BlownStep :=
  let breath := ((((noise * parameter) >>> 15) * 26214) >>> 15) + 26214
  let delayed := Physical.mix a b fraction
  let delta := ((((-3891 : Int32) * ((delayed >>> 1) + lp)) >>> 12)) - breath
  let reed := Digital.clip (((delta * (-1229 : Int32)) >>> 12) + 22938)
  let out := Digital.clip (((delta * reed) >>> 15) + breath)
  { lp := delayed >>> 1, bore := out.toInt16,
    filter := (((coefficient * out) + ((4096 - coefficient) * filter)) >>> 12).toInt16 }

/-- The result of one flute sample: the low-pass state, the two DC-blocker states, the samples written into the jet
and bore lines, and the output. -/
structure FlutedStep where
  lp : Int32
  dcX : Int32
  dcY : Int32
  jet : UInt8
  bore : UInt8
  out : Int16

/-- Flute: where the jet's delayed value falls on the 257-entry jet curve: the value limited to 0 to 65535, then
its top 8 bits. -/
@[inline] def Physical.jetIndex (jetValue : Int32) : UInt32 :=
  let limited := if jetValue < 0 then 0 else if jetValue > 65535 then 65535 else jetValue
  (limited >>> 8).toUInt32

/-- Flute: a bore and a jet delay line. Breath pressure comes from an envelope with noise on it (`intensity` says
how much); the bore's end reflects through a low-pass (`coefficient` out of 4096) and a DC blocker, and the jet's
delayed value passes through a saturating curve back into the bore. The line samples are 8 bits. -/
@[inline] def Physical.fluted (boreA boreB jetA jetB : Int32) (boreFraction jetFraction : UInt32)
    (excitation : UInt32) (noise intensity coefficient lp dcX dcY : Int32) : FlutedStep :=
  let boreValue := Physical.mix boreA boreB boreFraction <<< 9
  let jetValue := Physical.mix jetA jetB jetFraction <<< 9
  let steady := (Physical.blowingEnvelope excitation).toUInt32.toInt32 <<< 1
  let breath := steady + ((((noise * intensity) >>> 12) * steady) >>> 15)
  let lp' := (((-coefficient) * boreValue) + ((4096 - coefficient) * lp)) >>> 12
  let dcY' := ((4055 * dcY) >>> 12) + (lp' - dcX)
  let jet := (Physical.blowingJet (Physical.jetIndex jetValue)).toInt32 + (dcY' >>> 1)
  let out := Digital.clip (boreValue >>> 1)
  { lp := lp', dcX := lp', dcY := dcY', jet := ((breath - (dcY' >>> 1)) >>> 9).toUInt32.toUInt8,
    bore := (jet >>> 9).toUInt32.toUInt8, out := out.toInt16 }
