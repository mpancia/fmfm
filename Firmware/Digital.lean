import Firmware.Analog

set_option compiler.extract_closed false

/-!
# Digital oscillators with small state, one sample at a time

Port of the FM, feedback FM, chaotic FM, triple ring modulator, toy and digital modulation engines of Braids
(`digital_oscillator.cc`, Emilie Gillet, MIT). Like `Firmware/Analog.lean`: pure scalar functions, one result
structure per engine, each field exported on its own by `Firmware/DigitalApi.lean`, loops and buffers in
`voices/digital_glue.c`. Lean shifts bind tighter than `*` and `+`, so shifted products are parenthesized.
-/

/-- One entry of Braids' moderate-overdrive wave shaper (257 entries), looked up by C. Trusted data. -/
@[extern "fm1_braids_ws_moderate_overdrive"] opaque Digital.overdriveTable (index : UInt32) : Int16

/-- The result of one FM sample: both phases and the sample. -/
structure FmStep where
  phase : UInt32
  modPhase : UInt32
  out : Int16

/-- Two-operator FM: the modulator, scaled by `index` (0 to 32767), bends the carrier's phase. A sync pulse
restarts both. -/
@[inline] def Digital.fm (phase modPhase inc modInc : UInt32) (index : Int32) (sync : UInt8) : FmStep :=
  let p := if sync != 0 then 0 else phase + inc
  let m := (if sync != 0 then 0 else modPhase) + modInc
  let pm := ((Analog.sineAt m * index) <<< 2).toUInt32
  { phase := p, modPhase := m, out := (Analog.sineAt (p + pm)).toInt16 }

/-- The result of one feedback-FM or chaotic-FM sample: both phases, the last sample (fed back) and the sample. -/
structure FeedbackStep where
  phase : UInt32
  modPhase : UInt32
  previous : Int16
  out : Int16

/-- FM where the carrier's last output feeds the modulator. `attenuation` (0 to 32767) lowers the index for high
notes. -/
@[inline] def Digital.feedbackFm (phase modPhase inc modInc : UInt32) (previous : Int16) (index attenuation : Int32)
    (sync : UInt8) : FeedbackStep :=
  let p := if sync != 0 then 0 else phase + inc
  let m := (if sync != 0 then 0 else modPhase) + modInc
  let depth := (index * attenuation) >>> 15
  let fed := (previous.toInt32 <<< 14).toUInt32
  let pm := ((Analog.sineAt (m + fed) * depth) <<< 1).toUInt32
  let sample := (Analog.sineAt (p + pm)).toInt16
  { phase := p, modPhase := m, previous := sample, out := sample }

/-- FM where the carrier's output speeds the modulator up and down, which makes it wander. -/
@[inline] def Digital.chaoticFm (phase modPhase inc modInc : UInt32) (index : Int32) (sync : UInt8) : FeedbackStep :=
  let p := if sync != 0 then 0 else phase + inc
  let m := if sync != 0 then 0 else modPhase
  let pm := ((Analog.sineAt m * index) <<< 1).toUInt32
  let sample := (Analog.sineAt (p + pm)).toInt16
  let m' := m + (modInc >>> 8) * ((129 : Int32) + (sample.toInt32 >>> 9)).toUInt32
  { phase := p, modPhase := m', previous := sample, out := sample }

/-- The result of one ring-modulator sample: the three phases and the sample. -/
structure RingStep where
  phase : UInt32
  mod1 : UInt32
  mod2 : UInt32
  out : Int16

/-- A sine multiplied by two more sines, then run through a soft-clipping curve. `phase` already includes the
quarter-cycle offset of the C++ loop. -/
@[inline] def Digital.ringMod (phase mod1 mod2 inc inc1 inc2 : UInt32) (sync : UInt8) : RingStep :=
  let p := if sync != 0 then 0 else phase + inc
  let m1 := (if sync != 0 then 0 else mod1) + inc1
  let m2 := (if sync != 0 then 0 else mod2) + inc2
  let a := ((Analog.sineAt p * Analog.sineAt m1) >>> 16).toInt16.toInt32
  let b := ((a * Analog.sineAt m2) >>> 16).toInt16.toInt32
  let shaped := Analog.shape Digital.overdriveTable ((b + 32768) &&& 0xFFFF).toUInt32
  { phase := p, mod1 := m1, mod2 := m2, out := shaped.toInt16 }

/-- The result of one toy sample: the phase, the held sample, the counter and the sample. -/
structure ToyStep where
  phase : UInt32
  held : UInt8
  counter : UInt16
  out : Int16

/-- The toy's sample-and-hold: at four times the sample rate, hold a bit-twiddled value of the phase for `count`
taps, and smooth with a four-tap filter. `x` is the pattern parameter (0 to 255). -/
@[inline] def Digital.toy (phase inc : UInt32) (held : UInt8) (counter count : UInt16) (x : UInt8) (sync : UInt8) :
    ToyStep :=
  let start := if sync != 0 then 0 else phase
  let pick (p : UInt32) : UInt8 :=
    ((((p >>> 24) ^^^ (x.toUInt32 <<< 1)) &&& (~~~x.toUInt32)) + (x.toUInt32 >>> 1)).toUInt8
  let p1 := start + inc
  let r1 := counter ≥ count
  let h1 := if r1 then pick p1 else held
  let c1 := (if r1 then 0 else counter) + 1
  let p2 := p1 + inc
  let r2 := c1 ≥ count
  let h2 := if r2 then pick p2 else h1
  let c2 := (if r2 then 0 else c1) + 1
  let p3 := p2 + inc
  let r3 := c2 ≥ count
  let h3 := if r3 then pick p3 else h2
  let c3 := (if r3 then 0 else c2) + 1
  let p4 := p3 + inc
  let r4 := c3 ≥ count
  let h4 := if r4 then pick p4 else h3
  let c4 := (if r4 then 0 else c3) + 1
  let filtered : UInt32 := 10530 * h1.toUInt32 + 14751 * h2.toUInt32 + 16384 * h3.toUInt32 + 14751 * h4.toUInt32
  { phase := p4, held := h4, counter := c4, out := ((filtered >>> 8) - 28208).toUInt16.toInt16 }

/-- The result of one digital-modulation sample. -/
structure ModulationStep where
  phase : UInt32
  symbolPhase : UInt32
  count : UInt16
  filter : Int32
  data : UInt8
  out : Int16

/-- A phase-shift-keyed carrier: a stream of 2-bit symbols (a preamble, then bytes from a smoothed `parameter`)
chooses which of four phases the carrier takes. -/
@[inline] def Digital.modulation (phase inc symbolPhase symbolInc : UInt32) (count : UInt16) (filter : Int32)
    (data : UInt8) (parameter : Int32) : ModulationStep :=
  let p := phase + inc
  let sp := symbolPhase + symbolInc
  let tick := sp < symbolInc
  let count1 := if tick then (count + 1) else count
  let boundary := tick && (count1 &&& 3) == 0
  let count2 := if boundary && count1 ≥ 64 + 4 * 256 then 0 else count1
  let byteTime := count2 ≥ 64
  let filter' := if boundary && byteTime then ((filter * 3) + parameter) >>> 2 else filter
  let data' : UInt8 :=
    if tick then
      (if boundary then
        (if count2 < 32 then 0x00 else if count2 < 48 then 0x99 else if count2 < 64 then 0xCC else
          (filter' >>> 7).toUInt32.toUInt8)
      else data >>> 2)
    else data
  let symbol := (data' &&& 3).toNat
  let qi : Int32 := if symbol == 0 || symbol == 3 then 23100 else -23100
  let ii : Int32 := if symbol == 0 || symbol == 1 then 23100 else -23100
  let i := Analog.sineAt p
  let q := Analog.sineAt (p + 0x40000000)
  { phase := p, symbolPhase := sp, count := count2, filter := filter', data := data',
    out := (((qi * q) >>> 15) + ((ii * i) >>> 15)).toInt16 }

/-- Braids' `CLIP`: limit to the symmetric 16-bit range, -32767 to 32767. -/
@[inline] def Digital.clip (x : Int32) : Int32 := if x < -32767 then -32767 else if x > 32767 then 32767 else x

/-- Braids' `Mix` of two signed 16-bit values by a 16-bit balance (0 is all `a`). -/
@[inline] def Digital.mix (a b : Int32) (balance : UInt32) : Int32 :=
  ((a * (65535 - balance).toInt32 + b * balance.toInt32) >>> 16).toInt16.toInt32

/-- An unsigned 16-bit table at a 32-bit phase, the two nearest entries blended (Braids' unsigned `Interpolate824`). -/
@[inline] def Digital.lutAt (table : UInt32 → UInt16) (phase : UInt32) : UInt32 :=
  let a := (table (phase >>> 24)).toUInt32
  let b := (table ((phase >>> 24) + 1)).toUInt32
  (a + (((b - a) * ((phase >>> 8) &&& 0xFFFF)) >>> 16)).toUInt16.toUInt32
