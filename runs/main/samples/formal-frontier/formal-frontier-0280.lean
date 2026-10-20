public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ)

variable (R : Type u) [CommRing R] [Algebra K R]

include K

@[simp]
theorem infinitesimalAdditiveMulEquivPoints_symm_coordinate
    (f : (Spec (.of R)).asOver (Spec (.of K)) ⟶
      (infinitesimalAdditiveGroupScheme K p m).X) :
    ((infinitesimalAdditiveMulEquivPoints K p m R).symm f).toAdd.val =
      ((Spec.mapMulEquiv (R := K) (S := infinitesimalAdditiveCoordinateRing K p m)
        (T := R)).symm f).ofConv (infinitesimalAdditiveCoordinate K p m) := rfl

end AlgebraicGeometry
end
end
