public section

namespace Polynomial.Sequence

open Module Submodule

variable {R : Type*} [Semiring R] (S : Polynomial.Sequence R)

section Ring

variable {R : Type*} [Ring R] (S : Polynomial.Sequence R)

/-- Every polynomial sequence with unit leading coefficients is a basis of `R[X]`. -/
noncomputable def basisOfIsUnitLeadingCoeff
    (hCoeff : ∀ i, IsUnit (S i).leadingCoeff) :
    Basis ℕ R R[X] :=
  Basis.mk (S.linearIndependent_of_isRightRegular_leadingCoeff fun i =>
      (hCoeff i).isRegular.right)
    (eq_top_iff.mp (S.span hCoeff))

end Ring
end Polynomial.Sequence
end
