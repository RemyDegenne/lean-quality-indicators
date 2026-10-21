namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval6600 (x : Key → ℝ) : Integer.Sparse.eval row6600 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -2, -1, 1, 1, 0] GramFunctions.Block2.form6) x := by
  rw [rowCheck6600, Integer.Sparse.eval_collectBalanced, rawRowCheck6600]

end MUB6.Certificate.GramRows
end OAI
