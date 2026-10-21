namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval18777 (x : Key → ℝ) : Integer.Sparse.eval row18777 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block5.form0) x := by
  rw [rowCheck18777, Integer.Sparse.eval_collectBalanced, rawRowCheck18777]

end MUB6.Certificate.GramRows
end OAI
