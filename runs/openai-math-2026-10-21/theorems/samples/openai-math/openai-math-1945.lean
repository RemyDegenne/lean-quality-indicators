namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergedZero133 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged133 x = 0 := by
  rw [mergeCheck133, Integer.Sparse.eval_merge]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData
end OAI
