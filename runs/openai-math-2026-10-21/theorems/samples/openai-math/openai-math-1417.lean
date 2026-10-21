namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval8650 (x : Key → ℝ) : Integer.Sparse.eval row8650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![3, 0, -2, 0, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck8650, Integer.Sparse.eval_collectBalanced, rawRowCheck8650]

end MUB6.Certificate.GramRows
end OAI
