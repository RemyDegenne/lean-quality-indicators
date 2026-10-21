namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval1294 (x : Key → ℝ) : Integer.Sparse.eval row1294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck1294, Integer.Sparse.eval_collectBalanced, rawRowCheck1294]

end MUB6.Certificate.GramRows
end OAI
