namespace P2MW.S_NeronModelInfra_exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace Topology

universe u

namespace P2mLaw535G

section Agree

variable {R : Type u} [CommRing R]
  {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
  (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
  (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
  {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R)) (ι τ : SchemeHomOver y y')
  [IsOpenImmersion ι.1] [IsOpenImmersion τ.1]

def U2' : (pullback y y).Opens := U2 y U m a ha ⊓ (pullback.snd y y ⁻¹ᵁ Ub y U a ha)

end Agree
end P2mLaw535G
end
end P2MW.S_NeronModelInfra_exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section
