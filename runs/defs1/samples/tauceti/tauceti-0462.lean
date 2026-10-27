public section

open WithConv

namespace TauCeti.Cocharacter

variable {R H A B : Type*} [CommSemiring R] [Semiring H]

variable [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]

section Bialgebra

variable [_root_.Bialgebra R H]

variable (A) in
/-- The constant-point inclusion `M(A) → M(A[X])`, pullback of points along `A → A[X]`. -/
noncomputable def constPolyPoint :
    WithConv (H →ₐ[R] A) →* WithConv (H →ₐ[R] Polynomial A) :=
  AlgHom.mapValue (IsScalarTower.toAlgHom R A (Polynomial A))

end Bialgebra
end TauCeti.Cocharacter
end
