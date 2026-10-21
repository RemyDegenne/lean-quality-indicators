namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval18372 (x : Key → ℝ) : Integer.Sparse.eval row18372 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, -1, -1, 0, 1, -1] GramFunctions.Block4.form19) x := by
  rw [rowCheck18372, Integer.Sparse.eval_collectBalanced, rawRowCheck18372]

end MUB6.Certificate.GramRows
end OAI
