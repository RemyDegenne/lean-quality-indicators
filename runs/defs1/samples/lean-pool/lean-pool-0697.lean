public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace Core

section

open scoped BigOperators

open Finset Matrix Polynomial

variable {K : Type*} [Field K]

/-- Matrix of field checks for one SAT constraint family. -/
def sourceSATFamilyFieldMatrix
    (F : Formula) [Fintype K]
    (points : Finset K)
    (variablePlace : Fin F.variableCount → K)
    (momentBudget : ℕ)
    (family : sourceSATConstraintFamily F momentBudget) :
    Matrix
      (Fin (sourceSATFamilyRowCount F points momentBudget family))
      (Fin (sourceSATTableDimension F K points)) K :=
  LinearMap.toMatrix'
    (sourceSATFamilyLinearMap F points variablePlace momentBudget family)

end
end Core
end GapCVP
end
end
