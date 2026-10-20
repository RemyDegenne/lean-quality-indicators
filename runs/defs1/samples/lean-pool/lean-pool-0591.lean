@[expose] public section

noncomputable section

section

@[expose] public section

namespace LeanCert.Engine

open LeanCert.Core

/-- Check if expression is bounded in interval [lo, hi] -/
def checkBoundsDyadic (e : Expr) (ρ : IntervalDyadicEnv) (lo hi : ℚ)
    (cfg : DyadicConfig := {}) : Bool :=
  let result := LeanCert.Internal.Dyadic.evalUnchecked e ρ cfg
  result.lowerBoundedBy lo && result.upperBoundedBy hi

end LeanCert.Engine
end
end
end
end
