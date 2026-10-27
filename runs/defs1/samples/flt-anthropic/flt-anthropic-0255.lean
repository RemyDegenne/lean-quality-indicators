namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_iso_forall_unitAutSection_eq_one_of_forall_transition_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

open L5G.UA

namespace L5G

p2m_open

section G

variable {Y V B : Scheme.{u}} (𝓜 : Y.Modules)

noncomputable def genRestrict (ι : V ⟶ Y) (j : B ⟶ Y) (k : B ⟶ V) (e : k ≫ ι = j)
    (τ : (Scheme.Modules.pullback ι).obj 𝓜 ≅ SheafOfModules.unit V.ringCatSheaf) :
    (Scheme.Modules.pullback j).obj 𝓜 ≅ SheafOfModules.unit B.ringCatSheaf :=
  ((pullbackCongr e).app 𝓜).symm ≪≫ ((pullbackComp k ι).app 𝓜).symm ≪≫
    (Scheme.Modules.pullback k).mapIso τ ≪≫ pullbackUnitIso k

end G
end L5G
end P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_iso_forall_unitAutSection_eq_one_of_forall_transition_eq_one
