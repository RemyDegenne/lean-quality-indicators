namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist

set_option autoImplicit false

set_option linter.unusedSectionVars false

p2m_open

namespace ToricHeckeAlg

open AddMonoidAlgebra

variable {κ : Type*} [Field κ]

attribute [local instance] instCoeFunAddMonoidAlgebra

section separation

variable {G : Type*} [AddCommGroup G]

def evHom (κ : Type*) [Field κ] (u : G) : (Multiplicative G →* κ) →* κ where
  toFun F := F (Multiplicative.ofAdd u)
  map_one' := rfl
  map_mul' _ _ := rfl

end separation
end ToricHeckeAlg
end P2MW.S_ModularCurve_JHNeronObjectAtP_exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist
