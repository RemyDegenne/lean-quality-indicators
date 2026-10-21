namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval17043 (x : Key → ℝ) : Integer.Sparse.eval row17043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -1, -1, 2] GramFunctions.Block4.form0) x := by
  rw [rowCheck17043, Integer.Sparse.eval_collectBalanced, rawRowCheck17043]

end MUB6.Certificate.GramRows
end OAI
