namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval3582 (x : Key → ℝ) : Integer.Sparse.eval row3582 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block1.form8) x := by
  rw [rowCheck3582, Integer.Sparse.eval_collectBalanced, rawRowCheck3582]

end MUB6.Certificate.GramRows
end OAI
