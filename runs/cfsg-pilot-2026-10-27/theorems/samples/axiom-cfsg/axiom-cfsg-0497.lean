public section

namespace CFSG.RankThree.PartTwo.Sec18.Item183K

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G] {A M K S : Subgroup G} {c : G}

theorem inf_noncyclic_of_not_cyclic (h : Hyp183 G A M c K)
    (hC : ¬ ∃ x : G, sectionCentralizer A K (CFSG.Open.pCoreOf 2 K) ⊆
      (Subgroup.zpowers x : Set G)) :
    ¬ ∃ x : G, ((A ⊓ K : Subgroup G) : Set G) ⊆ (Subgroup.zpowers x : Set G) := by
  obtain ⟨S, hS⟩ := exists_sylowS h
  exact inf_noncyclic_of_not_cyclic_aux h hS hC

end CFSG.RankThree.PartTwo.Sec18.Item183K
end
