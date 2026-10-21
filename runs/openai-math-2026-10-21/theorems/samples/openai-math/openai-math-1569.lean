namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval16491 (x : Key → ℝ) : Integer.Sparse.eval row16491 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -1, 0, -2, 1, 1] GramFunctions.Block4.form11) x := by
  rw [rowCheck16491, Integer.Sparse.eval_collectBalanced, rawRowCheck16491]

end MUB6.Certificate.GramRows
end OAI
