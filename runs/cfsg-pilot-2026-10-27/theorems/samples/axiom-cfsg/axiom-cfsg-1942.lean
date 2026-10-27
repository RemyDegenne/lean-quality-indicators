public section

namespace CFSG.RankThree.PartTwo.Sec21.U4OddLines

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

open CFSG.RankThree.PartOne.KFU (diagU diagU_val apply_eq_zero_of_commute_diagU)

variable {K : Type} [Field K] {f : ℕ}

theorem blkSU2_le (h : UnitaryFieldData 2 f K) : blkSU2 f K ≤ unitarySU 2 f K 4 := by
  rintro _ ⟨X, hX, rfl⟩
  obtain ⟨hdet, hgram⟩ := (mem_unitarySU_iff h).1 hX
  refine (mem_unitarySU_iff h).2 ⟨?_, ?_⟩
  · rw [coe_blkGL2, det_blk2]
    exact hdet
  · rw [coe_blkGL2, blk2_gram, hgram, blk2_one]

end CFSG.RankThree.PartTwo.Sec21.U4OddLines
end
