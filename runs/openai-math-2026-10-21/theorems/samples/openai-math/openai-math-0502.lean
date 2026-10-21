namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval1255 (x : Key → ℝ) : Integer.Sparse.eval row1255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block1.form4) x := by
  rw [rowCheck1255, Integer.Sparse.eval_collectBalanced, rawRowCheck1255]

end MUB6.Certificate.GramRows
end OAI
