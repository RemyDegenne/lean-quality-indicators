public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace Core

section

open scoped BigOperators

open Matrix Finset Polynomial

variable {K : Type*} [Field K]

/-- GapCVP reduction support. -/
def rootSupportPolynomial
    {h : ℕ} (roots : Fin h → K) : K[X] :=
  ∏ i : Fin h, (Polynomial.X - Polynomial.C (roots i))

end
end Core
end GapCVP
end
end
