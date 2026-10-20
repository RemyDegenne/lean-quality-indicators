namespace P2MW.S_ModularCurve_exists_kaehlerDifferential_stalk_and_ringHom_res_eq_mapOfRingHom_cuspSection_of_ratCurveModel_compat_of_neZero

set_option autoImplicit false

open scoped TensorProduct

p2m_open

namespace GenFF

universe u

section K1

variable {Y X : Scheme.{u}} (h : Y ⟶ X) [IsOpenImmersion h] [IsIntegral Y] [IsIntegral X]

theorem germ_ffIso_hom_top :
    X.presheaf.germ ⊤ (genericPoint X) trivial ≫ (ffIso h).hom =
      h.appTop ≫ Y.presheaf.germ ⊤ (genericPoint Y) trivial :=
  germ_ffIso_hom h ⊤ trivial

end K1
end GenFF
end P2MW.S_ModularCurve_exists_kaehlerDifferential_stalk_and_ringHom_res_eq_mapOfRingHom_cuspSection_of_ratCurveModel_compat_of_neZero
