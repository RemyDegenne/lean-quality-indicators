public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ)

variable (R : Type u) [CommRing R] [Algebra K R]

include K

/-- Affine points of the quotient group scheme are exactly nilpotent elements,
with their additive group law. -/
@[expose] def infinitesimalAdditiveMulEquivPoints :
    Multiplicative (infinitesimalAdditiveSubgroup K p m R) ≃*
      ((Spec (.of R)).asOver (Spec (.of K)) ⟶ (infinitesimalAdditiveGroupScheme K p m).X) :=
  (infinitesimalAdditiveMulEquivAlgHom K p m R).trans
    (Spec.mapMulEquiv (R := K) (S := infinitesimalAdditiveCoordinateRing K p m) (T := R))

end AlgebraicGeometry
end
end
