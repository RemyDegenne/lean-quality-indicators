namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mSepKer

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem isClosedImmersion_one (L : RelativeGroupLaw K f) [IsSeparated f] :
    IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
  have h : IsClosedImmersion ((L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f) := by
    rw [(L.one _).2]; infer_instance
  exact IsClosedImmersion.of_comp (L.one (𝟙 (Spec (CommRingCat.of K)))).1 f

end P2mSepKer
end
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
