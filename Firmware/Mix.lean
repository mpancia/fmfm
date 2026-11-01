set_option compiler.extract_closed false

/-!
The arithmetic of the mix in `dinghy.c`: each voice's level glides toward its gate, its sample is scaled by
the sound's gain and the level, a share goes to the reverb bus, and the reverb's wet signal is scaled on the
way back. The C keeps the loops and the buffers and calls these once a sample.
-/

/-- The level one sample later: it rises by `up` or falls by `down` toward `gate` and stops at the gate rather
than passing it. -/
def Mix.envelopeStep (amp gate up down : Int32) : Int32 :=
  if amp < gate then
    let raised := amp + up
    if raised > gate then gate else raised
  else if amp > gate then
    let lowered := amp - down
    if lowered < gate then gate else lowered
  else amp

/-- A voice's sample for the mix: the Braids sample times the sound's gain (256 = 1) and the level
(130048 = full, the top of `play`'s gate). -/
def Mix.voiceSample (sample : Int16) (gain : UInt16) (amp : Int32) : Int32 :=
  (((sample.toInt32 * gain.toUInt32.toInt32) >>> 8) * (amp >>> 4)) >>> 15

/-- The share of a voice's sample that goes to the reverb bus: the bus is left plus right, so the sample is
doubled, then scaled by `send` (256 = all). -/
def Mix.sendSample (s : Int32) (send : UInt16) : Int32 :=
  (s * 2 * send.toUInt32.toInt32) >>> 8

/-- The reverb's wet sample scaled by the Q15 return gain. The product needs 64 bits; a shift is cheap on the
chip, a 64-bit division is not. -/
def Mix.wetSample (wet gain : Int32) : Int32 :=
  ((wet.toInt64 * gain.toInt64) >>> 15).toInt32

/-- The mix held within 524287 before `platform.c` multiplies it by the master gain (at most 4088): anything
louder would wrap in that product. Sixteen times full scale, so the limit is never reached by the dry mix
and only by an extreme wet return. -/
def Mix.limit (x : Int32) : Int32 :=
  if x > 524287 then 524287 else if x < -524287 then -524287 else x

/-- An effect's return into the mix: the wet sample times its gain, added, and held within the limit. The
delay goes in first, then the reverb, each through this. -/
def Mix.mixIn (mix wet gain : Int32) : Int32 := Mix.limit (mix + Mix.wetSample wet gain)

/-- The left gain of a pan setting, Q15: a quarter cosine in steps of 5 percent (pan 0 is hard left, 50 the middle,
100 hard right), so a sound keeps its power as it moves. A setting between steps goes to the nearest step, which
makes the left and right steps add up to the quarter turn and so the two gains to equal power exactly. -/
def Mix.panLeft (pan : UInt32) : Int32 :=
  match (min pan 100 + 2) / 5 with
  | 0 => 32767 | 1 => 32666 | 2 => 32365 | 3 => 31864 | 4 => 31164 | 5 => 30274 | 6 => 29197 | 7 => 27939
  | 8 => 26510 | 9 => 24917 | 10 => 23170 | 11 => 21281 | 12 => 19261 | 13 => 17121 | 14 => 14876 | 15 => 12540
  | 16 => 10126 | 17 => 7650 | 18 => 5126 | 19 => 2571 | _ => 0

/-- The right gain: the left gain of the mirrored setting. -/
def Mix.panRight (pan : UInt32) : Int32 := Mix.panLeft (100 - min pan 100)

/-- A voice's sample on one side: the sample times that side's Q15 gain. The sample is within 65024 and the
gain within 32767, so the product fits 32 bits. -/
def Mix.panSample (s gain : Int32) : Int32 := (s * gain) >>> 15

/-- C entry: the level one sample later. -/
@[export fm1_mix_envelope_step]
def mixEnvelopeStep (amp gate up down : Int32) : Int32 := Mix.envelopeStep amp gate up down

/-- C entry: a voice's sample for the mix. -/
@[export fm1_mix_voice_sample]
def mixVoiceSample (sample : Int16) (gain : UInt16) (amp : Int32) : Int32 := Mix.voiceSample sample gain amp

/-- C entry: a voice's share for the reverb bus. -/
@[export fm1_mix_send_sample]
def mixSendSample (s : Int32) (send : UInt16) : Int32 := Mix.sendSample s send

/-- C entry: the wet sample scaled by the return gain. -/
@[export fm1_mix_wet_sample]
def mixWetSample (wet gain : Int32) : Int32 := Mix.wetSample wet gain

/-- C entry: the mix held within what the master gain can scale. -/
@[export fm1_mix_limit]
def mixLimit (x : Int32) : Int32 := Mix.limit x

/-- C entry: the left pan gain. -/
@[export fm1_mix_pan_left]
def mixPanLeft (pan : UInt32) : Int32 := Mix.panLeft pan

/-- C entry: the right pan gain. -/
@[export fm1_mix_pan_right]
def mixPanRight (pan : UInt32) : Int32 := Mix.panRight pan

/-- C entry: a voice's sample on one side. -/
@[export fm1_mix_pan_sample]
def mixPanSample (s gain : Int32) : Int32 := Mix.panSample s gain

/-- C entry: an effect's return added to the mix, within the limit. -/
@[export fm1_mix_in]
def mixIn (mix wet gain : Int32) : Int32 := Mix.mixIn mix wet gain
