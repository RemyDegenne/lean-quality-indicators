public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Proof

open scoped commutatorElement

section Elementary

variable {G : Type*} [Group G]

theorem mem_normalizer_sup {w : G} {H K : Subgroup G} (hH : w ∈ Subgroup.normalizer (H : Set G))
    (hK : w ∈ Subgroup.normalizer (K : Set G)) :
    w ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

end Elementary
end CFSG.RankThree.PartTwo.Sec11.Item1119Proof
end
