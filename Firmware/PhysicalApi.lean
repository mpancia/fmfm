import Firmware.Physical

set_option compiler.extract_closed false

/-! C entry points for `Firmware/Physical.lean`: one function per result field. -/

/-- `comb`: the sample written into the delay line. -/
@[export fm1_comb_feedback] def combFeedback (input : Int32) (a : Int32) (b : Int32) (fraction : Int32) (resonance : Int32) : Int16 :=
  (Physical.comb input a b fraction resonance).feedback

/-- `comb`: the sample. -/
@[export fm1_comb_out] def combOut (input : Int32) (a : Int32) (b : Int32) (fraction : Int32) (resonance : Int32) : Int16 :=
  (Physical.comb input a b fraction resonance).out

/-- `comb`: the resonance setting bent for finer control at the extremes. -/
@[export fm1_comb_resonance] def combResonance (parameter : Int32) : Int32 := Physical.combResonance parameter

/-- `pluck`: the value that fills one place of a new string. -/
@[export fm1_pluck_fill] def pluckFill (old noise : Int32) : Int16 := Physical.pluckFill old noise

/-- `pluck`: 1 if this place of the string is averaged this time. -/
@[export fm1_pluck_updates] def pluckUpdates (word probability : UInt32) : UInt8 := Physical.pluckUpdates word probability

/-- `pluck`: the low-pass step of the string loop. -/
@[export fm1_pluck_average] def pluckAverage (a b loss : Int32) : Int16 := Physical.pluckAverage a b loss

/-- `pluck`: the string read between two entries. -/
@[export fm1_pluck_read] def pluckRead (a b : Int32) (phase : UInt32) : Int32 := Physical.pluckRead a b phase

/-- `physical`: a sum limited to 16 bits, the sample of the engines that run at half rate. -/
@[export fm1_physical_out] def physicalOut (sum : Int32) : Int16 := (Digital.clip sum).toInt16

/-- `physical`: the in-between sample of the engines that run at half rate. -/
@[export fm1_physical_mid] def physicalMid (sum previous : Int32) : Int16 := Physical.halfSum (Digital.clip sum) previous

/-- `bowed`: the bridge low-pass state after the sample. -/
@[export fm1_bowed_lp] def bowedLp (bridgeA : Int32) (bridgeB : Int32) (nutA : Int32) (nutB : Int32) (bridgeFraction : UInt32) (neckFraction : UInt32) (lp : Int32) (excitation : UInt32) (bow : Int32) (y0 : Int32) (y1 : Int32) : Int32 :=
  (Physical.bowed bridgeA bridgeB nutA nutB bridgeFraction neckFraction lp excitation bow y0 y1).lp

/-- `bowed`: the byte written into the neck line. -/
@[export fm1_bowed_neck] def bowedNeck (bridgeA : Int32) (bridgeB : Int32) (nutA : Int32) (nutB : Int32) (bridgeFraction : UInt32) (neckFraction : UInt32) (lp : Int32) (excitation : UInt32) (bow : Int32) (y0 : Int32) (y1 : Int32) : UInt8 :=
  (Physical.bowed bridgeA bridgeB nutA nutB bridgeFraction neckFraction lp excitation bow y0 y1).neck

/-- `bowed`: the byte written into the bridge line. -/
@[export fm1_bowed_bridge] def bowedBridge (bridgeA : Int32) (bridgeB : Int32) (nutA : Int32) (nutB : Int32) (bridgeFraction : UInt32) (neckFraction : UInt32) (lp : Int32) (excitation : UInt32) (bow : Int32) (y0 : Int32) (y1 : Int32) : UInt8 :=
  (Physical.bowed bridgeA bridgeB nutA nutB bridgeFraction neckFraction lp excitation bow y0 y1).bridge

/-- `bowed`: the body filter's new state. -/
@[export fm1_bowed_biquad] def bowedBiquad (bridgeA : Int32) (bridgeB : Int32) (nutA : Int32) (nutB : Int32) (bridgeFraction : UInt32) (neckFraction : UInt32) (lp : Int32) (excitation : UInt32) (bow : Int32) (y0 : Int32) (y1 : Int32) : Int32 :=
  (Physical.bowed bridgeA bridgeB nutA nutB bridgeFraction neckFraction lp excitation bow y0 y1).biquad

/-- `bowed`: the sample. -/
@[export fm1_bowed_out] def bowedOut (bridgeA : Int32) (bridgeB : Int32) (nutA : Int32) (nutB : Int32) (bridgeFraction : UInt32) (neckFraction : UInt32) (lp : Int32) (excitation : UInt32) (bow : Int32) (y0 : Int32) (y1 : Int32) : Int16 :=
  (Physical.bowed bridgeA bridgeB nutA nutB bridgeFraction neckFraction lp excitation bow y0 y1).out

/-- `blown`: the low-pass state after the sample. -/
@[export fm1_blown_lp] def blownLp (noise : Int32) (a : Int32) (b : Int32) (fraction : UInt32) (lp : Int32) (parameter : Int32) (filter : Int32) (coefficient : Int32) : Int32 :=
  (Physical.blown noise a b fraction lp parameter filter coefficient).lp

/-- `blown`: the sample written into the bore. -/
@[export fm1_blown_bore] def blownBore (noise : Int32) (a : Int32) (b : Int32) (fraction : UInt32) (lp : Int32) (parameter : Int32) (filter : Int32) (coefficient : Int32) : Int16 :=
  (Physical.blown noise a b fraction lp parameter filter coefficient).bore

/-- `blown`: the output filter's state, which is the sample. -/
@[export fm1_blown_filter] def blownFilter (noise : Int32) (a : Int32) (b : Int32) (fraction : UInt32) (lp : Int32) (parameter : Int32) (filter : Int32) (coefficient : Int32) : Int16 :=
  (Physical.blown noise a b fraction lp parameter filter coefficient).filter

/-- `fluted`: the low-pass state after the sample. -/
@[export fm1_fluted_lp] def flutedLp (boreA : Int32) (boreB : Int32) (jetA : Int32) (jetB : Int32) (boreFraction : UInt32) (jetFraction : UInt32) (excitation : UInt32) (noise : Int32) (intensity : Int32) (coefficient : Int32) (lp : Int32) (dcX : Int32) (dcY : Int32) : Int32 :=
  (Physical.fluted boreA boreB jetA jetB boreFraction jetFraction excitation noise intensity coefficient lp dcX dcY).lp

/-- `fluted`: the DC blocker's input state. -/
@[export fm1_fluted_dcx] def flutedDcx (boreA : Int32) (boreB : Int32) (jetA : Int32) (jetB : Int32) (boreFraction : UInt32) (jetFraction : UInt32) (excitation : UInt32) (noise : Int32) (intensity : Int32) (coefficient : Int32) (lp : Int32) (dcX : Int32) (dcY : Int32) : Int32 :=
  (Physical.fluted boreA boreB jetA jetB boreFraction jetFraction excitation noise intensity coefficient lp dcX dcY).dcX

/-- `fluted`: the DC blocker's output state. -/
@[export fm1_fluted_dcy] def flutedDcy (boreA : Int32) (boreB : Int32) (jetA : Int32) (jetB : Int32) (boreFraction : UInt32) (jetFraction : UInt32) (excitation : UInt32) (noise : Int32) (intensity : Int32) (coefficient : Int32) (lp : Int32) (dcX : Int32) (dcY : Int32) : Int32 :=
  (Physical.fluted boreA boreB jetA jetB boreFraction jetFraction excitation noise intensity coefficient lp dcX dcY).dcY

/-- `fluted`: the byte written into the jet line. -/
@[export fm1_fluted_jet] def flutedJet (boreA : Int32) (boreB : Int32) (jetA : Int32) (jetB : Int32) (boreFraction : UInt32) (jetFraction : UInt32) (excitation : UInt32) (noise : Int32) (intensity : Int32) (coefficient : Int32) (lp : Int32) (dcX : Int32) (dcY : Int32) : UInt8 :=
  (Physical.fluted boreA boreB jetA jetB boreFraction jetFraction excitation noise intensity coefficient lp dcX dcY).jet

/-- `fluted`: the byte written into the bore line. -/
@[export fm1_fluted_bore] def flutedBore (boreA : Int32) (boreB : Int32) (jetA : Int32) (jetB : Int32) (boreFraction : UInt32) (jetFraction : UInt32) (excitation : UInt32) (noise : Int32) (intensity : Int32) (coefficient : Int32) (lp : Int32) (dcX : Int32) (dcY : Int32) : UInt8 :=
  (Physical.fluted boreA boreB jetA jetB boreFraction jetFraction excitation noise intensity coefficient lp dcX dcY).bore

/-- `fluted`: the sample. -/
@[export fm1_fluted_out] def flutedOut (boreA : Int32) (boreB : Int32) (jetA : Int32) (jetB : Int32) (boreFraction : UInt32) (jetFraction : UInt32) (excitation : UInt32) (noise : Int32) (intensity : Int32) (coefficient : Int32) (lp : Int32) (dcX : Int32) (dcY : Int32) : Int16 :=
  (Physical.fluted boreA boreB jetA jetB boreFraction jetFraction excitation noise intensity coefficient lp dcX dcY).out

