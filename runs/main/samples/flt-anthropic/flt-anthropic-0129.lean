namespace P2MW.S_AlgebraicGeometry_exists_isProper_twoAffineLineCover

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

noncomputable section

namespace P1E85

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

attribute [local instance] MvPolynomial.gradedAlgebra

variable (S : Type u) [CommRing S]

scoped instance finiteType_𝒜0 : Algebra.FiniteType (↥(𝒜 S 0)) (MvPolynomial (Fin 2) S) := by
  classical
  exact ⟨⟨(Finset.univ : Finset (Fin 2)).image MvPolynomial.X, by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact adjoin_X_eq_top S⟩⟩

section Overlap

variable (S : Type u) [CommRing S]

open HomogeneousLocalization

theorem B₀₁_toLaurent (p : Polynomial S) : B₀₁ S (Polynomial.toLaurent p) = m₀ S (B₀ S p) := by
  letI := (m₀ S).toAlgebra
  haveI := isLocalization_m₀ S
  rw [← LaurentPolynomial.algebraMap_eq_toLaurent]
  exact IsLocalization.ringEquivOfRingEquiv_eq _ p

end Overlap
end P1E85
end
end P2MW.S_AlgebraicGeometry_exists_isProper_twoAffineLineCover
