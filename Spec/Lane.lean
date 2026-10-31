import Firmware.Lane
import Spec.Notes

/-- A lane is consistent: its settings are in range and its running state agrees with itself. These are the
facts the lane's behaviour depends on. -/
structure Lane.Valid (l : Lane) : Prop where
  stepsPositive : 1 ≤ l.steps
  hitsFit : l.hits ≤ l.steps
  divPositive : 1 ≤ l.div
  maskNotEmpty : l.mask ≠ 0
  maskSmall : l.mask < 4096
  lowFloor : 12 ≤ l.low
  lowCeiling : l.low ≤ 96
  spanPositive : 1 ≤ l.span
  spanFits : l.low + l.span ≤ 120
  gatePositive : 1 ≤ l.gate
  probFits : l.prob ≤ 100
  loopLengthPositive : 1 ≤ l.rule.amount
  loopLengthFits : l.rule.amount ≤ Notes.regLen
  notesValid : NoteState.Valid l.span l.rule.amount l.notes
  countBelowDiv : l.count < l.div
  stepBelowSteps : l.step < l.steps
  /-- A note is sounding exactly when its gate has time left. -/
  soundingHasTimer : l.playing.isSome = true ↔ 0 < l.gateLeft
  timerWithinGate : l.gateLeft ≤ l.gate
