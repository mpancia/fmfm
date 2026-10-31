/-!
# Held-note tracker

Remembers which notes are down and which one was played last. This is the first piece of
firmware logic written with ordinary Lean data (a structure and a list), so it needs the
small Lean runtime in `rt/lean_rt.c`. Compare `Kernels.lean`, which uses integers only.

The C side keeps one `Tracker` and replaces it after every event:
`t = fm1_tracker_press(t, note)`. Every exported function takes ownership of its `Tracker`
argument (exports cannot borrow), so C calls `lean_inc(t)` first when it wants to keep `t`.
-/

set_option compiler.extract_closed false

/-- The notes held now, most recent first, and the note played last (255 if none yet). -/
structure Tracker where
  held : List UInt8
  last : UInt8

/-- No note has been played. -/
def Tracker.empty : Tracker := { held := [], last := 255 }

/-- Note `n` goes down. It becomes the most recent held note and the last note played.
If it was already held, it moves to the front instead of appearing twice. -/
def Tracker.press (t : Tracker) (n : UInt8) : Tracker :=
  { held := n :: t.held.filter (· != n), last := n }

/-- Note `n` comes up. `last` stays as it is: it means "last played", not "last held". -/
def Tracker.release (t : Tracker) (n : UInt8) : Tracker :=
  { t with held := t.held.filter (· != n) }

/-- How many notes are held. -/
def Tracker.count (t : Tracker) : UInt32 := t.held.length.toUInt32

/-- C entry: a tracker with no notes. -/
@[export fm1_tracker_new]
def trackerNew (_ : Unit) : Tracker := Tracker.empty

/-- C entry: `Tracker.press`. -/
@[export fm1_tracker_press]
def trackerPress (t : Tracker) (n : UInt8) : Tracker := t.press n

/-- C entry: `Tracker.release`. -/
@[export fm1_tracker_release]
def trackerRelease (t : Tracker) (n : UInt8) : Tracker := t.release n

/-- C entry: the note played last, or 255. -/
@[export fm1_tracker_last]
def trackerLast (t : Tracker) : UInt8 := t.last

/-- C entry: how many notes are held. -/
@[export fm1_tracker_count]
def trackerCount (t : Tracker) : UInt32 := t.count

/-- No note appears twice in the held list, whatever happens. -/
theorem Tracker.press_nodup (t : Tracker) (n : UInt8) (h : t.held.Nodup) : (t.press n).held.Nodup := by
  simp only [Tracker.press, List.nodup_cons]
  exact ⟨by simp, h.filter _⟩

/-- Releasing keeps the held list free of duplicates. -/
theorem Tracker.release_nodup (t : Tracker) (n : UInt8) (h : t.held.Nodup) : (t.release n).held.Nodup :=
  h.filter _

/-- After a release, the note is not held. -/
theorem Tracker.release_not_held (t : Tracker) (n : UInt8) : n ∉ (t.release n).held := by
  simp [Tracker.release]

/-- The empty tracker satisfies the no-duplicates condition, so the theorems above apply from power-on. -/
example : Tracker.empty.held.Nodup := List.nodup_nil
