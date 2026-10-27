public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Module CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.ComponentInitial

section Orders

variable {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem u42_card_orthogonalGroup_nine_four (hK : Nat.card K = 9) {Q : QuadraticForm K W}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hm : finrank K W = 4) :
    414720 < Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have hm' : finrank K W = 2 * (1 + 1) := hm
  by_cases hp : IsPlusType Q
  · have := natCard_orthogonalGroup_of_type hQ hm' (ε := 1) (Or.inl ⟨rfl, hp⟩)
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = c at this ⊢
    rw [hK] at this
    norm_num [Finset.prod_Icc_succ_top] at this
    omega
  · have := natCard_orthogonalGroup_of_type hQ hm' (ε := -1) (Or.inr ⟨rfl, hp⟩)
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = c at this ⊢
    rw [hK] at this
    norm_num [Finset.prod_Icc_succ_top] at this
    omega

end Orders
end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
end
