namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval16458 (x : Key → ℝ) : Integer.Sparse.eval row16458 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 1, -2, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck16458, Integer.Sparse.eval_collectBalanced, rawRowCheck16458]

end MUB6.Certificate.GramRows
end OAI
