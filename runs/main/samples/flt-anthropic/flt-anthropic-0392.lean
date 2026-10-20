namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE

set_option autoImplicit false

p2m_open

universe u

namespace PV1TL

section coh

p2m_open

variable {T' T A' : Scheme.{u}}

lemma congr_unit {f f' : T' ⟶ T} (H : f = f') :
    (pullbackCongr H).hom.app (SheafOfModules.unit T.ringCatSheaf) ≫ (pullbackUnitIso f').hom =
      (pullbackUnitIso f).hom := by
  subst H; simp [pullbackCongr]

end coh
end PV1TL
end P2MW.S_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE
