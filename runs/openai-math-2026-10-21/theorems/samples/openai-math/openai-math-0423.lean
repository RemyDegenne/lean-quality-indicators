namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval6464 (x : Key → ℝ) : Integer.Sparse.eval row6464 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, 0, -2, -1] GramFunctions.Block2.form7) x := by
  rw [rowCheck6464, Integer.Sparse.eval_collectBalanced, rawRowCheck6464]

end MUB6.Certificate.GramRows
end OAI
