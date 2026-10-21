namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval16508 (x : Key → ℝ) : Integer.Sparse.eval row16508 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -1, -2] GramFunctions.Block4.form11) x := by
  rw [rowCheck16508, Integer.Sparse.eval_collectBalanced, rawRowCheck16508]

end MUB6.Certificate.GramRows
end OAI
