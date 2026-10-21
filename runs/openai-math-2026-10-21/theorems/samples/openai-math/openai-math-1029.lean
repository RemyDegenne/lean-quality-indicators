namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval8816 (x : Key → ℝ) : Integer.Sparse.eval row8816 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 2, 0, 0, 0, -3] GramFunctions.Block3.form9) x := by
  rw [rowCheck8816, Integer.Sparse.eval_collectBalanced, rawRowCheck8816]

end MUB6.Certificate.GramRows
end OAI
