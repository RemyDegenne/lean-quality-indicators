namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_section_eq_of_reducesToOrigin_of_originParam_eq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

namespace OSUniqAux

open HomogeneousLocalization MvPolynomial HomogeneousIdealQuotientGrading

section AwayCongr

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

def awayCongr {s s' : A} (e : s = s') : Away 𝒜 s ≃+* Away 𝒜 s' := by
  subst e; exact RingEquiv.refl _

end AwayCongr
end OSUniqAux
end P2MW.S_WeierstrassCurve_DrinfeldGlobal_section_eq_of_reducesToOrigin_of_originParam_eq
