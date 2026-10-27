public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

open CFSG.LieType.Ree.LargeReeCover (torusPair)

open scoped commutatorElement

namespace Setup

variable {G : Type} [Group G] [Finite G]
  (h : Setup G)

theorem pull_unpull {M : Subgroup G} (hM : M ≤ h.L) : h.pull (h.unpull M) = M := by
  rw [pull, unpull, subgroupOf, comap_map_eq_self_of_injective (subtype_injective _),
    map_comap_eq, range_emb, inf_eq_right.2 hM]

end Setup
end CFSG.LocalAnalysis.EvenBN.TwoF4
end
