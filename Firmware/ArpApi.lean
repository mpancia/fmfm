import Firmware.Arp

set_option compiler.extract_closed false

/-- C entry: a silent arpeggiator with a step of `div` ticks. -/
@[export fm1_arp_make]
def arpMake (div seed : UInt32) : Arp := Arp.make div.toNat seed

/-- C entry: mode (0 off, 1 up, 2 down, 3 up and down, 4 random, 5 as played), octaves, ticks a step, gate ticks. -/
@[export fm1_arp_set]
def arpSet (a : Arp) (mode octaves div gate : UInt32) : Arp := a.set mode.toNat octaves.toNat div.toNat gate.toNat

/-- C entry: a key pressed. -/
@[export fm1_arp_press]
def arpPress (a : Arp) (note : UInt32) : Arp := a.press note.toNat

/-- C entry: a key released. -/
@[export fm1_arp_release]
def arpRelease (a : Arp) (note : UInt32) : Arp := a.release note.toNat

/-- C entry: every key released. -/
@[export fm1_arp_clear]
def arpClear (a : Arp) : Arp := a.clear

/-- C entry: one clock tick. -/
@[export fm1_arp_tick]
def arpTick (a : Arp) : Arp := a.tick

/-- C entry: stop the sounding note. -/
@[export fm1_arp_silence]
def arpSilence (a : Arp) : Arp := a.silence

/-- C entry: the note the last tick started, or 255. -/
@[export fm1_arp_on]
def arpOn (a : Arp) : UInt32 := (a.on.getD 255).toUInt32

/-- C entry: the note the last tick stopped, or 255. -/
@[export fm1_arp_off]
def arpOff (a : Arp) : UInt32 := (a.off.getD 255).toUInt32

/-- C entry: how many notes are held. -/
@[export fm1_arp_held]
def arpHeld (a : Arp) : UInt32 := a.held.length.toUInt32
