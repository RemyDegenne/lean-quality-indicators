namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval3157 (x : Key → ℝ) : Integer.Sparse.eval row3157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -1, 0, -2, 2] GramFunctions.Block1.form5) x := by
  rw [rowCheck3157, Integer.Sparse.eval_collectBalanced, rawRowCheck3157]

end MUB6.Certificate.GramRows
end OAI
