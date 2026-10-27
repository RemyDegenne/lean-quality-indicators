public section

open ComplexConjugate InnerProductSpace Set

open scoped ComplexOrder NNReal Pointwise fwdDiff

namespace TauCeti

universe u

section

variable {V : Type u} {F : ℝ≥0 × V → ℂ}

/-- The first alternating time difference with step `h`:
`timeDifference h F (t, v) = F (t, v) - F (t + h, v)`. It is the negative of Mathlib's forward
difference `fwdDiff` applied in the time coordinate. -/
def timeDifference (h : ℝ≥0) (F : ℝ≥0 × V → ℂ) : ℝ≥0 × V → ℂ :=
  fun p => -fwdDiff h (fun t => F (t, p.2)) p.1

end
end TauCeti
end
