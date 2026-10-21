namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval17782 (x : Key → ℝ) : Integer.Sparse.eval row17782 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck17782, Integer.Sparse.eval_collectBalanced, rawRowCheck17782]

end MUB6.Certificate.GramRows
end OAI
