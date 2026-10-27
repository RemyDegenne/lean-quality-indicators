public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K]

theorem blk_one : blk (1 : Matrix (Fin 3) (Fin 3) K) 0 0 1 = 1 := by
  unfold blk
  rw [Matrix.fromBlocks_one]
  exact map_one blkE

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
end
