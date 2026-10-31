/-- Smoke-test definition so the build, `lake check` and `make run` have something real to exercise. Replace with the real project. -/
def greeting : String := "fmfm: toolchain OK"

/-- `greeting` is not empty. -/
theorem greeting_ne_empty : greeting ≠ "" := by decide
