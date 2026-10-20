public section

open scoped Nat

namespace TauCeti

namespace BrauerAlgebra

variable {R : Type*} [CommSemiring R] {δ : R} {k : ℕ}

/-- The basis element of the Brauer algebra at the Brauer diagram `D`. -/
noncomputable def of (D : BrauerDiagram k) : BrauerAlgebra R δ k :=
  ofCoeff (Finsupp.single D 1)

end BrauerAlgebra
end TauCeti
end
