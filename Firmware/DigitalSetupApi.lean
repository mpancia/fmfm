import Firmware.DigitalSetup

set_option compiler.extract_closed false

/-! C entry points for `Firmware/DigitalSetup.lean`, one per block quantity. `voices/digital_setup_glue.c`
includes the generated code and `voices/braids/digital_oscillator.cc` calls them once per block. -/

/-- The FM ratio parameter snapped to the quantizer table. -/
@[export fm1_digital_setup_fm_quantized_parameter] def digitalSetupFmQuantizedParameter (param : Int16) :
    Int16 :=
  DigitalSetup.fmQuantizedParameter param

/-- The FM modulator's phase step, halved. -/
@[export fm1_digital_setup_fm_modulator_increment] def digitalSetupFmModulatorIncrement
    (pitch param : Int16) : UInt32 :=
  DigitalSetup.fmModulatorIncrement pitch param

/-- The feedback FM's attenuation, 0 to 32767. -/
@[export fm1_digital_setup_feedback_attenuation] def digitalSetupFeedbackAttenuation (pitch param : Int16) :
    Int32 :=
  DigitalSetup.feedbackAttenuation pitch param

/-- The phase step of one of the ring modulator's modulators. -/
@[export fm1_digital_setup_ring_increment] def digitalSetupRingIncrement (pitch param : Int16) : UInt32 :=
  DigitalSetup.ringIncrement pitch param

/-- The toy's oversampled phase step. -/
@[export fm1_digital_setup_toy_increment] def digitalSetupToyIncrement (increment : UInt32) : UInt32 :=
  DigitalSetup.toyIncrement increment

/-- How many samples the toy holds each one. -/
@[export fm1_digital_setup_toy_decimation] def digitalSetupToyDecimation (param : Int16) : UInt16 :=
  DigitalSetup.toyDecimation param

/-- How many low bits the toy drops. -/
@[export fm1_digital_setup_toy_bits] def digitalSetupToyBits (param : Int16) : UInt8 :=
  DigitalSetup.toyBits param

/-- The digital modulation's symbol stream phase step. -/
@[export fm1_digital_setup_modulation_symbol_increment] def digitalSetupModulationSymbolIncrement
    (pitch param : Int16) : UInt32 :=
  DigitalSetup.modulationSymbolIncrement pitch param

/-- The delay-line length for a pitch, as a 16.16 fraction of samples. -/
@[export fm1_digital_setup_delay] def digitalSetupDelay (pitch : Int16) : UInt32 :=
  DigitalSetup.delay pitch
