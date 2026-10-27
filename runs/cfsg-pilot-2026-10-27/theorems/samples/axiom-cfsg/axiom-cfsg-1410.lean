public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type*} [Group G] {L : Subgroup G}

section Basic

variable {C : Type*} [Group C]

theorem isCyclic_map_symm (e : L ≃* C) {A : Subgroup C} (hA : IsCyclic A) :
    IsCyclic ((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) :=
  isCyclic_of_surjective (mapSymmMulEquiv e A).symm.toMonoidHom
    (mapSymmMulEquiv e A).symm.surjective

end Basic
end CFSG.SeitzReduction.LinearPilot
end
