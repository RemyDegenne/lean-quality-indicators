public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.X10

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.LieType.Ree (ReeTag)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

variable {K : Type} [Field K] [Finite K]

theorem noPSp4_of_lieModel_psl_two_two_three (hO : LieOrderFormulasInput) {L : Type} [Group L]
    (h : LieModel L .PSL 2 2 3) : NoPSp4 3 L := by
  have hadm : StatedLieAdmissible .PSL 2 2 3 := by
    refine ⟨Nat.prime_two, by norm_num, le_rfl, ?_, ?_⟩ <;> decide
  obtain ⟨hfin, hord, -⟩ := hO L .PSL 2 2 3 hadm h
  have h1 : lieOrderDivisor .PSL 2 (2 ^ 3) = 1 := by decide
  have h2 : lieOrderNumerator .PSL 2 (2 ^ 3) = 504 := by decide
  rw [h1, h2, mul_one] at hord
  exact noPSp4_of_card_le hO Nat.prime_three (by decide) hord.le

end CFSG.ComponentClassification.Burgoyne.X10
end
