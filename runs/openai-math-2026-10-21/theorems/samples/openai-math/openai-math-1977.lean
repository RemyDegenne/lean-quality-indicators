namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval9750 (x : Key → ℝ) : Integer.Sparse.eval row9750 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, 0, 1, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck9750, Integer.Sparse.eval_collectBalanced, rawRowCheck9750]

end MUB6.Certificate.GramRows
end OAI
