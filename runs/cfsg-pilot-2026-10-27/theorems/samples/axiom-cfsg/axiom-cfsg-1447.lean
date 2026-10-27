public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

section Generic

variable {Q : Type} [Group Q] [Finite Q]

theorem u4x_mem_normalizer_sup {A B : Subgroup Q} {g : Q} (hA : g ∈ normalizer (A : Set Q))
    (hB : g ∈ normalizer (B : Set Q)) : g ∈ normalizer ((A ⊔ B : Subgroup Q) : Set Q) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

end Generic
end CFSG.LocalAnalysis.UniquenessCase.UC22
end
