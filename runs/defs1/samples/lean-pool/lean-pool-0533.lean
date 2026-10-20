public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace Core

section

open scoped BigOperators

open Polynomial Matrix Finset

variable {K : Type*} [Field K]

/-- GapCVP reduction support. -/
def genericHankelDenominator (h : ℕ) (moments : ℕ → K[X]) : K[X] :=
  leadingHankelDet moments h

end
end Core
end GapCVP
end
end
