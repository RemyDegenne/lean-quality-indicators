public section

open MonoidAlgebra Representation

open scoped MatrixGroups

namespace TauCeti.TraceFormulaMatrixModule

variable {k : Type*} {n : ℤ}

section Semiring

variable [Semiring k]

@[simp]
theorem coeff_upperTriangularSum (x : TraceFormulaMatrixModule n) :
    (upperTriangularSum k n).coeff x = (upperTriangularReps n).indicator 1 x := by
  classical
  simp [upperTriangularSum, Finsupp.single_apply, Set.indicator_apply]

end Semiring
end TauCeti.TraceFormulaMatrixModule
end
