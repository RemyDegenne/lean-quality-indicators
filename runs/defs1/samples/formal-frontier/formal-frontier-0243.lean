public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ)

/-- The image of the additive coordinate in the quotient Hopf algebra. -/
@[expose] def infinitesimalAdditiveCoordinate : infinitesimalAdditiveCoordinateRing K p m :=
  (Ideal.Quotient.mkₐ K (infinitesimalAdditiveIdeal K p m)) (additiveGroupCoordinate K)

end AlgebraicGeometry
end
end
