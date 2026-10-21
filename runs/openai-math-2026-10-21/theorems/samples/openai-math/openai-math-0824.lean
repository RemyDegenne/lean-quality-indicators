namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval16762 (x : Key → ℝ) : Integer.Sparse.eval row16762 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, -1, -1, 0, 2, 0] GramFunctions.Block4.form3) x := by
  rw [rowCheck16762, Integer.Sparse.eval_collectBalanced, rawRowCheck16762]

end MUB6.Certificate.GramRows
end OAI
