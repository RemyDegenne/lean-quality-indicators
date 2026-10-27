namespace P2MW.S_ModularCurve_exists_ringHom_cover_modularFunctionFieldBar_of_ratCurveModel_of_neZero

set_option autoImplicit false

p2m_open

namespace GenFF

universe u

section Iota

variable (p : ℕ) (q : ℕ) [Fact q.Prime]
  {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt q))) [IsIntegral X]
  (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p))
  (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ)))) [IsIso e₀]

noncomputable def iota0 (U : X.Opens) (hU : genericPoint X ∈ U) : Γ(X, U) →+* ↥(modularFunctionFieldFull p) :=
  haveI := isOpenImmersion_hImm p q c M₀ e₀
  M₀.ffEquiv.symm.toRingHom.comp
    ((ffIso (hImm p q c M₀ e₀)).hom.hom.comp (X.presheaf.germ U (genericPoint X) hU).hom)

end Iota
end GenFF
end P2MW.S_ModularCurve_exists_ringHom_cover_modularFunctionFieldBar_of_ratCurveModel_of_neZero
