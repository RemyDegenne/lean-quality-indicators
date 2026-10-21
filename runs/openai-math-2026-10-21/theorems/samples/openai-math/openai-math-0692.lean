namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergedZero1478 (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1478 x = 0 := by
  rw [mergeCheck1478, Integer.Sparse.eval_merge]
  rw [mergedZero1477 x h]
  simp only [Integer.Sparse.eval_scale, h, mul_zero, add_zero]

end MUB6.Certificate.MixedData
end OAI
