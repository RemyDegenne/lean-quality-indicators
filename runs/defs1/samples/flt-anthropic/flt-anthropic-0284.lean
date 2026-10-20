namespace P2MW.S_M4aHerbrand_exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

p2m_open

namespace M4aHerbrand

namespace TowerPkgProof

p2m_open

noncomputable section

open TensorProduct M4aHerbrand.Bridge M4aHerbrand.GenuineDescent

open scoped TensorProduct

section Beta

variable (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
  [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M]

abbrev βU : (AdeleRing (𝓞 F) F)ˣ →* (AdeleRing (𝓞 M) M)ˣ := Units.map (genuineBaseChange F M).β.toMonoidHom

end Beta
end
end TowerPkgProof
end M4aHerbrand
end P2MW.S_M4aHerbrand_exists_hom_res_ideles_and_ideleClassGroup_injective_range_eq_invariants_of_isScalarTower
