public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Block

variable {F : Type*} [Field F] {e r n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem blkMat_map {K : Type*} [Field K] (φ : F →+* K) (σ : (Fin e × ι) ⊕ Fin r ≃ Fin n)
    (X : ι → Matrix (Fin e) (Fin e) F) :
    (blkMat σ X).map φ = blkMat σ (fun t => (X t).map φ) := by
  rw [blkMat_apply, blkMat_apply, reindex_apply, reindex_apply, ← submatrix_map,
    fromBlocks_map, blockDiagonal_map _ _ (map_zero φ)]
  simp [Matrix.map_zero, Matrix.map_one, map_zero, map_one]

end Block
end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
end
