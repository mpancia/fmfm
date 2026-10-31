/-!
# Kernels that run on the FM-1

Everything in this file is compiled to C by Lean and linked into the firmware
(`make kernels` checks that it links with no Lean runtime). Rules:

* Only fixed-width integers and `Bool`. No `Nat`, `Int`, `String`, `Array`, structures:
  those need Lean's allocator, which the chip does not have.
* The chip has no FPU and no 64-bit division.
* `extract_closed false` stops Lean from hoisting constants into lazily initialised
  globals, which would pull in the Lean runtime.
-/

set_option compiler.extract_closed false

/-- Oscillator phase after one sample: add the step, wrap at 2^32.
A full cycle is 2^32, so wrapping is exactly "start the next cycle". -/
@[export fm1_phase_step]
def phaseStep (phase step : UInt32) : UInt32 := phase + step

/-- Adding a step never loses more than a full cycle: the result is the true sum
modulo 2^32. -/
theorem phaseStep_spec (phase step : UInt32) :
    (phaseStep phase step).toNat = (phase.toNat + step.toNat) % 2 ^ 32 := by
  simp [phaseStep, UInt32.toNat_add]
