public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate)

open scoped MatrixGroups commutatorElement

section Matrices

variable {K : Type} [Field K] {k : ℕ}

theorem transpose_swapBlk : (swapBlk : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K)ᵀ = swapBlk := by
  rw [swapBlk, coe_reindexAlgEquiv, transpose_reindex, fromBlocks_transpose, transpose_zero,
    transpose_one]

end Matrices
end CFSG.ComponentClassification.RankTwoClassical
end
