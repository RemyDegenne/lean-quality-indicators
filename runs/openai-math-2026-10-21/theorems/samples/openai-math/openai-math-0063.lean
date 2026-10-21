namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval11177 (x : Key → ℝ) : Integer.Sparse.eval row11177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck11177, Integer.Sparse.eval_collectBalanced, rawRowCheck11177]

end MUB6.Certificate.GramRows
end OAI
