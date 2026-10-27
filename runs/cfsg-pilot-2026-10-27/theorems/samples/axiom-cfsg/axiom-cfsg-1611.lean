public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise

open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace QD

section Q

variable {D : Subgroup G}

variable (hR : IsRootClass R)

include hR

theorem lambdaSet_subset_isolatedSet [Finite G] (hD : D ∈ R) :
    lambdaSet R D ⊆ isolatedSet R D := fun _ hB =>
  ⟨⟨hB.1.1, hB.1.2.2⟩, fun _ hC hop => not_commuting_of_opposite_of_mem_lambdaSet hR hC.1
    hop.symm (mem_lambdaSet_comm hD hB) hC.2.symm⟩

end Q
end QD
end CFSG.Timmesfeld.ARS
end
