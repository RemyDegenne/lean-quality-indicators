public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

open scoped Pointwise

section Bar

variable {G : Type} [Group G] [Finite G]

theorem uc22s21ru3c_isSolvable_barImage {M T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 ↥T) :
    Group.IsSolvable ↥(barImage M T) := by
  have h1 : IsPGroup 2 ↥(T.subgroupOf M) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm
  have h2 : IsPGroup 2 ↥(barImage M T) := h1.map _
  haveI := h2.isNilpotent
  infer_instance

end Bar
end CFSG.LocalAnalysis.UniquenessCase.UC22
end
