public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ)

variable (R : Type u) [CommRing R] [Algebra K R]

include K

theorem infinitesimalAdditiveConvolution_coordinate
    (r s : infinitesimalAdditiveSubgroup K p m R) :
    ((infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd r) *
      infinitesimalAdditiveMulEquivAlgHom K p m R (.ofAdd s)).ofConv
        (infinitesimalAdditiveCoordinate K p m)) = r.val + s.val := by
  rw [← infinitesimalAdditiveMulEquivAlgHom_add,
    infinitesimalAdditiveMulEquivAlgHom_coordinate]
  rfl

end AlgebraicGeometry
end
end
