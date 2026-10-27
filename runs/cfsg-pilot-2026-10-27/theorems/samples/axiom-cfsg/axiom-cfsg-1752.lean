public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.U54InvRank

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups

open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.U5K.Hyp

open CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.F431.Un CFSG.Quasithin.H13.Sec53F.Unit

open CFSG.Blueprint (LieModel)

section Transport

variable {K : Type} [Field K] (h : UnitaryFieldData 2 2 K) (ψ : K ≃+* GF16)

theorem tr16_gram : tr16 ψ (hypGram 2 1 GF16) = hypGram 2 1 K := by
  ext a b
  rw [tr16_apply, hypGram_apply, hypGram_apply]
  split_ifs <;> simp

end Transport
end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.U54InvRank
end
