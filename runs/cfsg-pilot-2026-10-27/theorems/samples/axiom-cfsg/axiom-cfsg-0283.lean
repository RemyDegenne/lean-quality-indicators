public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

open CFSG.Blueprint (LieModel)

theorem card_eq_ordTwistedA_three_of_isSUn_four {X : Type} [Group X] {a : ℕ} (h : IsSUn X 4 a)
    (ha : 1 ≤ a) : Nat.card X = ordTwistedA 3 (2 ^ a) := by
  obtain ⟨K, _, _, hKcard, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.ClassicalInvolution.Asc77.SCH.card_statedSU_four
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hKcard),
    ← NoTransv.ordSU_four_two_pow_eq_ordTwistedA_three ha, CFSG.SeitzReduction.F4Pilot.ordSU_four]
  ring

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
end
