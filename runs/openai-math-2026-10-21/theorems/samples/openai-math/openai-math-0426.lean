namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval2585 (x : Key → ℝ) : Integer.Sparse.eval row2585 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 2, 0, -1, 0, 0] GramFunctions.Block1.form7) x := by
  rw [rowCheck2585, Integer.Sparse.eval_collectBalanced, rawRowCheck2585]

end MUB6.Certificate.GramRows
end OAI
