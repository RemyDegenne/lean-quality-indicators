public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_three_mem_of_mem_normalizer {K : Subgroup G} {b k : G}
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (hb3 : b ^ 3 = 1) (hk : k ∈ K) :
    (b * k) ^ 3 ∈ K := by
  have e : (b * k) ^ 3 = (b * k * b⁻¹) * (b ^ 2 * k * (b ^ 2)⁻¹) * (b ^ 3 * k) := by
    rw [pow_three]
    group
  rw [e, hb3, one_mul]
  have hb2 : b ^ 2 ∈ Subgroup.normalizer (K : Set G) := pow_mem hb 2
  exact mul_mem (mul_mem ((Subgroup.mem_normalizer_iff.mp hb k).mp hk)
    ((Subgroup.mem_normalizer_iff.mp hb2 k).mp hk)) hk

end CFSG.RankThree.PartTwo.Sec17
end
