namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval233 (x : Key → ℝ) : Integer.Sparse.eval row233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block0.form2) x := by
  rw [rowCheck233, Integer.Sparse.eval_collectBalanced, rawRowCheck233]

end MUB6.Certificate.GramRows
end OAI
