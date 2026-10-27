public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig (coreSup
  TwoLines)

open scoped Pointwise commutatorElement

section General

variable {X : Type} [Group X] [Finite X]

theorem subgroupOf_map_subtype_of_le {H G : Subgroup X} (h : H ≤ G) :
    (H.subgroupOf G).map G.subtype = H := by
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h]

end General
end CFSG.RankThree.PartTwo.Sec14.Ronan148H
end
