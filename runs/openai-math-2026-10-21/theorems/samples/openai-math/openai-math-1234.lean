namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval19871 (x : Key → ℝ) : Integer.Sparse.eval row19871 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form4) x := by
  rw [rowCheck19871, Integer.Sparse.eval_collectBalanced, rawRowCheck19871]

end MUB6.Certificate.GramRows
end OAI
