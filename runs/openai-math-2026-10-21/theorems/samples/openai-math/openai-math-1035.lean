namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval373 (x : Key → ℝ) : Integer.Sparse.eval row373 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 1, -1, 0, 1, -2] GramFunctions.Block0.form2) x := by
  rw [rowCheck373, Integer.Sparse.eval_collectBalanced, rawRowCheck373]

end MUB6.Certificate.GramRows
end OAI
