namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval180 (x : Key → ℝ) : Integer.Sparse.eval row180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, -2, 2, 0, 0] GramFunctions.Block0.form1) x := by
  rw [rowCheck180, Integer.Sparse.eval_collectBalanced, rawRowCheck180]

end MUB6.Certificate.GramRows
end OAI
