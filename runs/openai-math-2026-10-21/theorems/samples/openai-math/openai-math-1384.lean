namespace OAI

namespace MUB6.Certificate.PairData

theorem pairMergedZero266 (x : Fin 271 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (rows k) x = 0) : Integer.Sparse.eval pairMerged266 x = 0 := by
  rw [pairMergeCheck266, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.PairData
end OAI
