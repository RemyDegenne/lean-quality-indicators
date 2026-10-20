namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_connectedSpace_pullback_toBase_specMap_ratLocalizedAt

set_option autoImplicit false

open scoped TensorProduct

p2m_reactivate

open scoped TensorProduct

p2m_reactivate

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped TensorProduct

noncomputable section

namespace FibreConnGeometry

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

variable (L : Type u) [CommRing L] [Algebra R L]

p2m_reactivate

variable {B0 B1 B01 : Type u} [CommRing B0] [Algebra R B0] [CommRing B1] [Algebra R B1]
  [CommRing B01] [Algebra R B01] (ρ0 : B0 →ₐ[R] B01) (ρ1 : B1 →ₐ[R] B01)
  (h0 : Spec (.of B0) ⟶ X) (h1 : Spec (.of B1) ⟶ X)
  (hh0 : h0 ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B0)))
  (hh1 : h1 ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B1)))

abbrev τ1 : B1 ⊗[R] L →ₐ[R] B01 ⊗[R] L := Algebra.TensorProduct.map ρ1 (AlgHom.id R L)

end FibreConnGeometry
end
end P2MW.S_AlgebraicCurve_TwoChartIntegralModel_connectedSpace_pullback_toBase_specMap_ratLocalizedAt
