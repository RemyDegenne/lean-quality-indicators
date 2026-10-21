namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval9832 (x : Key → ℝ) : Integer.Sparse.eval row9832 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -2, 1, -1] GramFunctions.Block3.form13) x := by
  rw [rowCheck9832, Integer.Sparse.eval_collectBalanced, rawRowCheck9832]

end MUB6.Certificate.GramRows
end OAI
