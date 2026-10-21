namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval4322 (x : Key → ℝ) : Integer.Sparse.eval row4322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block1.form6) x := by
  rw [rowCheck4322, Integer.Sparse.eval_collectBalanced, rawRowCheck4322]

end MUB6.Certificate.GramRows
end OAI
