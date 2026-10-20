set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))

theorem frameUnit_self (i : Fin (N + 1)) : frameUnit φ i i = 1 := by
  rw [frameUnit, ratio_self, map_one, map_one]
  rfl

end AlgebraicGeometry.ProjSpace
end
