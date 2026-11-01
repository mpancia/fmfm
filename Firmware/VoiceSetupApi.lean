import Firmware.VoiceSetup

set_option compiler.extract_closed false

/-! C entry points for `Firmware/VoiceSetup.lean`. `voices/voice_setup_glue.c` includes the generated code and
`voices/voice.cc` calls each once per block. -/

/-- The shape to play. -/
@[export fm1_voice_setup_shape] def voiceSetupShape (shape : UInt32) : UInt32 := VoiceSetup.shape shape

/-- The pitch as Braids holds it. -/
@[export fm1_voice_setup_pitch] def voiceSetupPitch (pitch : Int32) : Int16 := VoiceSetup.pitch pitch

/-- A timbre value as Braids holds it. -/
@[export fm1_voice_setup_parameter] def voiceSetupParameter (value : Int32) : Int16 :=
  VoiceSetup.parameter value
