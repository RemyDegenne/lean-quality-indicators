namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval6059 (x : Key → ℝ) : Integer.Sparse.eval row6059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, -1, 0, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck6059, Integer.Sparse.eval_collectBalanced, rawRowCheck6059]

end MUB6.Certificate.GramRows
end OAI
