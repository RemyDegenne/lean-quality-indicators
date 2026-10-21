namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval1759 (x : Key → ℝ) : Integer.Sparse.eval row1759 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -2, 1, -1] GramFunctions.Block1.form9) x := by
  rw [rowCheck1759, Integer.Sparse.eval_collectBalanced, rawRowCheck1759]

end MUB6.Certificate.GramRows
end OAI
