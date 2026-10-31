import Firmware.Digital

set_option compiler.extract_closed false

/-!
# Saw swarm, digital filters, vosim and harmonics, one sample at a time

Port of the matching engines of Braids (`digital_oscillator.cc`, Emilie Gillet, MIT), in the style of
`Firmware/Digital.lean`. Per-block setup (increments, cutoffs, the harmonic amplitudes) stays in C++.
-/

/-- One entry of Braids' bell-shaped window (257 entries), looked up by C. Trusted data. -/
@[extern "fm1_braids_lut_bell"] opaque Filters.bellTable (index : UInt32) : UInt16

/-- The bell window at a phase, with the two nearest entries blended. -/
@[inline] def Filters.bellAt (phase : UInt32) : UInt32 := Digital.lutAt Filters.bellTable phase

/-- The saw swarm's raw sample: seven saws (given as phases) added, then soft-clipped. -/
@[inline] def Filters.swarmShape (p0 p1 p2 p3 p4 p5 p6 : UInt32) : Int32 :=
  let sum : Int32 := (-28672 : Int32) + (p0 >>> 19).toInt32 + (p1 >>> 19).toInt32 + (p2 >>> 19).toInt32 +
    (p3 >>> 19).toInt32 + (p4 >>> 19).toInt32 + (p5 >>> 19).toInt32 + (p6 >>> 19).toInt32
  (Analog.shape Digital.overdriveTable ((sum + 32768).toUInt32)).toInt16.toInt32

/-- The result of one state-variable filter step: low-pass, band-pass and the high-pass output. -/
structure SvfStep where
  lp : Int32
  bp : Int32
  out : Int16

/-- One step of the swarm's high-pass: a state-variable filter with cutoff `f` and damping `damp`. -/
@[inline] def Filters.swarmFilter (sample f damp bp lp : Int32) : SvfStep :=
  let notch := sample - ((bp * damp) >>> 15)
  let lp' := Digital.clip (lp + ((f * bp) >>> 15))
  let hp := notch - lp'
  { lp := lp', bp := bp + ((f * hp) >>> 15), out := (Digital.clip hp).toInt16 }

/-- The result of one digital-filter sample. -/
structure FilterStep where
  phase : UInt32
  modPhase : UInt32
  squarePhase : UInt32
  integrator : Int32
  polarity : UInt8
  out : Int16

/-- Where the resonance phase restarts on each cycle (Braids' `kPhaseReset`): nothing, a half or a quarter cycle. -/
@[inline] def Filters.phaseReset (index : UInt8) : UInt32 :=
  if index == 0 then 0 else if index == 2 then 0x40000000 else 0x80000000

/-- The "digital filter" oscillators: a saw or triangle and a square, each windowing a sine at a resonant
frequency, with a type (0 to 3) choosing low-pass, peak, band-pass or high-pass. -/
@[inline] def Filters.digitalFilter (phase inc modPhase modInc squarePhase : UInt32) (integrator : Int32)
    (polarity filterType : UInt8) (parameter : Int32) (sync : UInt8) : FilterStep :=
  let p0 := phase + inc
  let m0 := modPhase + modInc
  let gain : UInt32 := (modInc >>> 14) &&& 0xFFFF
  let reset := sync != 0
  let p1 := if reset then 0 else p0
  let m1 := if reset then 0 else m0
  let sq0 := if reset then 0 else squarePhase
  let integ0 := if reset then 0 else integrator
  let pol0 : UInt8 := if reset then 1 else polarity
  let sq1 := sq0 + modInc
  let m2 := if p1 < inc then Filters.phaseReset filterType else m1
  let flip := (p1 <<< 1) < (inc <<< 1)
  let pol1 : UInt8 := if flip then (if pol0 != 0 then 0 else 1) else pol0
  let sq2 := if flip then Filters.phaseReset ((filterType &&& 1) + 2) else sq1
  let carrier := Analog.sineAt m2
  let squareCarrier := Analog.sineAt sq2
  let saw : UInt32 := (~~~(p1 >>> 16)) &&& 0xFFFF
  let doubleSaw : UInt32 := (~~~(p1 >>> 15)) &&& 0xFFFF
  let triangle : UInt32 := ((p1 >>> 15) ^^^ (if p1 &&& 0x80000000 != 0 then 0xFFFF else 0)) &&& 0xFFFF
  let window : Int32 := (if parameter < 16384 then saw else triangle).toInt32
  let pulse0 := (squareCarrier * doubleSaw.toInt32) >>> 16
  let pulse := if pol1 != 0 then 0 - pulse0 else pulse0
  let integ1 := Digital.clip (integ0 + ((pulse * gain.toInt32) >>> 16))
  let sawTri : Int32 :=
    if filterType &&& 2 != 0 then ((carrier * window) >>> 16).toInt16.toInt32
    else ((((window * (carrier + 32768)) >>> 16) - 32768).toInt16.toInt32)
  let square : Int32 :=
    if filterType &&& 2 != 0 then pulse.toInt16.toInt32
    else if filterType == 1 then ((pulse + integ1) >>> 1).toInt16.toInt32
    else integ1.toInt16.toInt32
  let raw : Int32 := if parameter < 16384 then parameter else ~~~parameter
  let balance : UInt32 := ((raw <<< 2).toUInt32) &&& 0xFFFF
  { phase := p1, modPhase := m2, squarePhase := sq2, integrator := integ1, polarity := pol1,
    out := (Digital.mix sawTri square balance).toInt16 }

/-- The result of one vosim sample. -/
structure VosimStep where
  phase : UInt32
  formant0 : UInt32
  formant1 : UInt32
  out : Int16

/-- Vosim: two sine formants under a bell window that restarts every cycle of the base pitch. -/
@[inline] def Filters.vosim (phase inc formant0 formant1 inc0 inc1 : UInt32) (sync : UInt8) : VosimStep :=
  let p := if sync != 0 then 0 else phase + inc
  let f0 := formant0 + inc0
  let f1 := formant1 + inc1
  let sample : Int32 := (24576 : Int32) + (Analog.sineAt f0 >>> 1) + (Analog.sineAt f1 >>> 2)
  let windowed := (sample * ((Filters.bellAt p).toInt32 >>> 1)) >>> 15
  let restart := p < inc
  let value : Int32 := if restart then 0 else windowed
  { phase := p, formant0 := if restart then 0 else f0, formant1 := if restart then 0 else f1,
    out := (value - 24576).toInt16 }

/-- One additive harmonic of the harmonics engine: its sine, scaled by its current amplitude. -/
@[inline] def Filters.harmonicSine (phase multiple : UInt32) (amplitude : Int32) : Int32 :=
  (Analog.sineAt (phase * multiple) * amplitude) >>> 15

/-- A harmonic's amplitude, a step closer to its target. -/
@[inline] def Filters.harmonicGlide (amplitude target : Int32) : Int32 := amplitude + ((target - amplitude) >>> 8)

/-- The harmonics engine's sample: the clipped sum. -/
@[inline] def Filters.harmonicsOut (sum : Int32) : Int32 := Digital.clip sum

/-- The in-between sample of the engines that run at half rate: the average of the clipped sum with the last one. -/
@[inline] def Filters.harmonicsMid (sum previous : Int32) : Int32 := (Digital.clip sum + previous) >>> 1
