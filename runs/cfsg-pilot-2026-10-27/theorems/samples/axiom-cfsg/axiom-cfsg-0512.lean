public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

open CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.RankThree.PartTwo.Sec3

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_normalizer_fourChar (S : Subgroup G) (k : Fin 4) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (fourChar S k : Set G) := by
  have h0 : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (fourChar S 0 : Set G) := by
    rw [Item181ThreeProof.fourChar_zero]
    exact Item181ThreeProof.normalizer_le_normalizer_omegaG S
  have h1 : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (fourChar S 1 : Set G) := by
    rw [Item181ThreeProof.fourChar_one]
    exact Item181ThreeProof.normalizer_le_normalizer_jG S 0
  have h2 : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (fourChar S 2 : Set G) := by
    rw [Item181ThreeProof.fourChar_two]
    exact (Item181ThreeProof.normalizer_le_normalizer_jG S 1).trans
      (Item181ThreeProof.normalizer_le_normalizer_omegaG (jG S 1))
  have h3 : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (fourChar S 3 : Set G) := by
    rw [Item181ThreeProof.fourChar_three]
    exact (Item181ThreeProof.normalizer_le_normalizer_jG S 2).trans
      (Item181ThreeProof.normalizer_le_normalizer_omegaG (jG S 2))
  fin_cases k
  exacts [h0, h1, h2, h3]

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
end
