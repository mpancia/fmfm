import Firmware.Patch

/-- Reading a lane back from its own bytes gives the lane, with the bytes after it untouched. -/
private theorem patchLane_ofBytes_bytes (l : PatchLane) (fits : l.Fits) (rest : List UInt8) :
    PatchLane.ofBytes (l.bytes ++ rest) = some (l, rest) := by
  obtain ⟨hits, steps, speed, scale, sound, low, span, algo, chance, amount, mutate, chord, level, send,
    seed⟩ := l
  simp only [PatchLane.Fits] at fits
  simp only [PatchLane.bytes, List.cons_append, List.nil_append, PatchLane.ofBytes]
  have byte : ∀ n, n < 256 → (UInt8.ofNat n).toNat = n := fun n h => UInt8.toNat_ofNat_of_lt' h
  have seedSplit : seed / 256 * 256 + seed % 256 = seed := Nat.div_add_mod' seed 256
  simp (disch := omega) only [byte, seedSplit]

/-- Saving a patch and loading the bytes back gives the same patch, for every patch the knobs can produce.
Why it matters: a user slot restores exactly what was saved, every lane setting and every global, with no
field lost, swapped or rounded on the way through flash. -/
theorem patch_decode_encode_round_trip (p : Patch) (fits : p.Fits) :
    Patch.decode (Patch.encode p) = some p := by
  obtain ⟨bpm, key, progression, rate, scaleLock, time, bright, amount, lane0, lane1, lane2, lane3⟩ := p
  have fitsAll := fits
  simp only [Patch.Fits] at fits
  obtain ⟨_, bpmLe, keyLt, progLt, _, lockLe, timeLe, brightLe, amountLe, fits0, fits1, fits2, fits3⟩ := fits
  have byte : ∀ n, n < 256 → (UInt8.ofNat n).toNat = n := fun n h => UInt8.toNat_ofNat_of_lt' h
  have last := patchLane_ofBytes_bytes lane3 fits3 []
  rw [List.append_nil] at last
  simp only [Patch.decode, Patch.encode, List.toList_toArray, Patch.bytes, List.cons_append,
    List.nil_append, List.append_assoc, Patch.ofBytes, guard, and_self, ite_true, bind, Option.bind,
    patchLane_ofBytes_bytes lane0 fits0, patchLane_ofBytes_bytes lane1 fits1,
    patchLane_ofBytes_bytes lane2 fits2, last, List.isEmpty_nil, Option.pure_def]
  simp (disch := omega) only [byte, fitsAll, ite_true]

/-- A patch that loads from a slot is one the knobs could have produced: every setting is in range.
Why it matters: a corrupt or foreign slot can never put an out-of-range sound index, scale or step count
into the firmware, where it would read past a table; such a slot loads as EMPTY instead. -/
theorem patch_decode_only_fits (bytes : ByteArray) (p : Patch) (loaded : Patch.decode bytes = some p) :
    p.Fits := by
  unfold Patch.decode at loaded
  split at loaded
  · split at loaded
    · rename_i fits; simp only [Option.some.injEq] at loaded; exact loaded ▸ fits
    · exact absurd loaded (by simp)
  · exact absurd loaded (by simp)

/-- Bytes that do not start with the marker read as no patch. -/
private theorem patch_ofBytes_wrong_marker (l : List UInt8) (wrong : l[0]? ≠ some 0xA7) :
    Patch.ofBytes l = none := by
  unfold Patch.ofBytes
  split
  · rename_i marker version bpm key prog rate lock time bright amount lanes
    simp at wrong
    simp [guard, wrong]
  · rfl

/-- A slot whose first byte is not the patch marker 0xA7 never loads.
Why it matters: a slot never written, or written by other software, is told apart by its first byte and
treated as empty rather than read as a scramble of settings. -/
theorem patch_decode_rejects_wrong_marker (bytes : ByteArray) (nonEmpty : 0 < bytes.size)
    (wrong : bytes[0] ≠ 0xA7) : Patch.decode bytes = none := by
  unfold Patch.decode
  have head : bytes.data.toList[0]? = some bytes[0] := by simp [ByteArray.getElem_eq_getElem_data]
  rw [patch_ofBytes_wrong_marker _ (by rw [head]; simpa using wrong)]

/-- A lane takes exactly 22 bytes off the front. -/
private theorem patchLane_ofBytes_length (l rest : List UInt8) (lane : PatchLane)
    (parsed : PatchLane.ofBytes l = some (lane, rest)) : l.length = rest.length + 22 := by
  unfold PatchLane.ofBytes at parsed
  split at parsed
  · simp only [Option.some.injEq, Prod.mk.injEq] at parsed
    obtain ⟨_, rfl⟩ := parsed
    simp
  · simp at parsed

/-- Bytes that read as a patch are exactly 98 long. -/
private theorem patch_ofBytes_length (l : List UInt8) (p : Patch) (parsed : Patch.ofBytes l = some p) :
    l.length = 98 := by
  unfold Patch.ofBytes at parsed
  split at parsed
  · rename_i marker version bpm key prog rate lock time bright amount lanes
    simp only [guard, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at parsed
    obtain ⟨_, _, ⟨lane0, rest0⟩, p0, ⟨lane1, rest1⟩, p1, ⟨lane2, rest2⟩, p2, ⟨lane3, rest3⟩, p3, _, empty,
      _⟩ := parsed
    have len0 := patchLane_ofBytes_length _ _ _ p0
    have len1 := patchLane_ofBytes_length _ _ _ p1
    have len2 := patchLane_ofBytes_length _ _ _ p2
    have len3 := patchLane_ofBytes_length _ _ _ p3
    simp at empty
    subst empty
    simp at len0 len1 len2 len3 ⊢
    omega
  · simp at parsed

/-- A slot that is not exactly 98 bytes long never loads.
Why it matters: a slot written by a firmware with a different patch layout is rejected whole instead of
being read field by field in the wrong places. -/
theorem patch_decode_rejects_wrong_size (bytes : ByteArray) (wrong : bytes.size ≠ 98) :
    Patch.decode bytes = none := by
  unfold Patch.decode
  split
  · rename_i p parsed
    have length := patch_ofBytes_length _ _ parsed
    simp at length
    exact absurd length wrong
  · rfl

/-- Every saved patch is 98 bytes long.
Why it matters: the C side reads exactly this many bytes back from a flash slot (`FM1_PATCH_BYTES`); a
different count would make every saved patch unloadable. -/
theorem patch_encode_size (p : Patch) : (Patch.encode p).size = 98 := by
  simp [Patch.encode, Patch.bytes, PatchLane.bytes, ByteArray.size]
