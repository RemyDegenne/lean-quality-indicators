namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval8738 (x : Key → ℝ) : Integer.Sparse.eval row8738 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -3, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck8738, Integer.Sparse.eval_collectBalanced, rawRowCheck8738]

end MUB6.Certificate.GramRows
end OAI
