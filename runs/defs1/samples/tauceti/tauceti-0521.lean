public section

open Matrix

open scoped TensorProduct

namespace TauCeti.SpStd

open LieAlgebra.Symplectic

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ)

/-- The diagonal matrix of the `i`-th simple coroot in the standard symplectic representation. -/
def cartanGeneratorMatrix (i : Fin (n + 1)) :
    Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℚ :=
  diagonal fun k => (weight n k i : ℚ)

end TauCeti.SpStd
end
