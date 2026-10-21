namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval17272 (x : Key → ℝ) : Integer.Sparse.eval row17272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -1, -1, 2, 0] GramFunctions.Block4.form12) x := by
  rw [rowCheck17272, Integer.Sparse.eval_collectBalanced, rawRowCheck17272]

end MUB6.Certificate.GramRows
end OAI
