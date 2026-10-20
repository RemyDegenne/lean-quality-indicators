public section

open WithConv

namespace TauCeti.GeneralLinear

universe w

variable (n p k : ℕ)

section Points

variable {A : Type w} [CommRing A] [ExpChar A p]

theorem pointsMulEquiv_iterateFrobeniusPoints
    (f : WithConv (coordinateHopfAlgebra ℤ n →ₐ[ℤ] A)) :
    pointsMulEquiv (R := ℤ) n (Bialgebra.iterateFrobeniusPoints p k f) =
      Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) (pointsMulEquiv (R := ℤ) n f) := by
  rw [pointsMulEquiv_apply, pointsMulEquiv_apply]
  exact pointToGeneralLinear_iterateFrobeniusPoints n p k f

end Points
end TauCeti.GeneralLinear
end
