namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval16164 (x : Key → ℝ) : Integer.Sparse.eval row16164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -1, 0, -2] GramFunctions.Block4.form1) x := by
  rw [rowCheck16164, Integer.Sparse.eval_collectBalanced, rawRowCheck16164]

end MUB6.Certificate.GramRows
end OAI
