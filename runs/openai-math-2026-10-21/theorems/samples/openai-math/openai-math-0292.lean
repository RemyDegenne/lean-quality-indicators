namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval995 (x : Key → ℝ) : Integer.Sparse.eval row995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block1.form3) x := by
  rw [rowCheck995, Integer.Sparse.eval_collectBalanced, rawRowCheck995]

end MUB6.Certificate.GramRows
end OAI
