namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval4211 (x : Key → ℝ) : Integer.Sparse.eval row4211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 1, 0, -1, 0, -2] GramFunctions.Block1.form16) x := by
  rw [rowCheck4211, Integer.Sparse.eval_collectBalanced, rawRowCheck4211]

end MUB6.Certificate.GramRows
end OAI
