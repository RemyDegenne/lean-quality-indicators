namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval11271 (x : Key → ℝ) : Integer.Sparse.eval row11271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck11271, Integer.Sparse.eval_collectBalanced, rawRowCheck11271]

end MUB6.Certificate.GramRows
end OAI
