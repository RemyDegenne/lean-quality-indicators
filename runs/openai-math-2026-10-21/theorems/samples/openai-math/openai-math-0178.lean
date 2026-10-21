namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval3403 (x : Key → ℝ) : Integer.Sparse.eval row3403 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, -2, 0] GramFunctions.Block1.form13) x := by
  rw [rowCheck3403, Integer.Sparse.eval_collectBalanced, rawRowCheck3403]

end MUB6.Certificate.GramRows
end OAI
