set_option warningAsError true

universe u v w w'

namespace NormForms

public section

open Module MvPolynomial

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

variable {ι : Type w} {κ : Type w'} [Fintype ι] [Fintype κ]

/-- The signed constant characteristic coefficient giving the coordinate norm form. -/
@[expose]
noncomputable def coordinateNormPolynomial (b : Basis ι K L) : MvPolynomial ι K := by
  classical
  let _ := Module.Free.of_basis b
  let _ := Module.Finite.of_basis b
  exact C ((-1 : K) ^ Module.finrank K L) *
    (LinearMap.polyCharpoly (Algebra.lmul K L).toLinearMap b).coeff 0

end
end NormForms
