namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval18067 (x : Key → ℝ) : Integer.Sparse.eval row18067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block4.form3) x := by
  rw [rowCheck18067, Integer.Sparse.eval_collectBalanced, rawRowCheck18067]

end MUB6.Certificate.GramRows
end OAI
