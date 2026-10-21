namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval1271 (x : Key → ℝ) : Integer.Sparse.eval row1271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block1.form4) x := by
  rw [rowCheck1271, Integer.Sparse.eval_collectBalanced, rawRowCheck1271]

end MUB6.Certificate.GramRows
end OAI
