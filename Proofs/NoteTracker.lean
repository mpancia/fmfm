import Firmware.NoteTracker

/-- With no duplicates before, pressing a note leaves no duplicates.
Why it matters: a note that is pressed twice cannot end up held twice, so one release always silences it. -/
theorem tracker_press_no_duplicates (tracker : Tracker) (note : UInt8) (clean : tracker.held.Nodup) :
    (tracker.press note).held.Nodup := by
  simp only [Tracker.press, List.nodup_cons]
  exact ⟨by simp, clean.filter _⟩

/-- With no duplicates before, releasing a note leaves no duplicates.
Why it matters: no sequence of presses and releases can ever build up a duplicate. -/
theorem tracker_release_no_duplicates (tracker : Tracker) (note : UInt8) (clean : tracker.held.Nodup) :
    (tracker.release note).held.Nodup :=
  clean.filter _

/-- A released note is no longer held.
Why it matters: after the key comes up the note is not in the list, so nothing keeps it sounding. -/
theorem tracker_release_not_held (tracker : Tracker) (note : UInt8) : note ∉ (tracker.release note).held := by
  simp [Tracker.release]
