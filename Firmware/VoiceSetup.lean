set_option compiler.extract_closed false

/-!
The voice's doorway into Braids (`braids_voice_set` in `voices/voice.cc`): the shape, pitch and two timbre
values the firmware sends, as the macro oscillator takes them. The firmware sends a MIDI note times 128 and
timbre values of 0 to 32767; Braids holds each in 16 bits. Scalar only.
-/

namespace VoiceSetup

/-- A shape the voice can play: one of Braids' 48, else the first. -/
@[inline] def shape (shape : UInt32) : UInt32 := if shape ≥ 48 then 0 else shape

/-- The pitch as Braids holds it: the low 16 bits of the 1/128-semitone pitch. -/
@[inline] def pitch (pitch : Int32) : Int16 := pitch.toInt16

/-- A timbre value as Braids holds it: its low 16 bits. -/
@[inline] def parameter (value : Int32) : Int16 := value.toInt16

end VoiceSetup
