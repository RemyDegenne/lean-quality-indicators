namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval5377 (x : Key → ℝ) : Integer.Sparse.eval row5377 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block2.form2) x := by
  rw [rowCheck5377, Integer.Sparse.eval_collectBalanced, rawRowCheck5377]

end MUB6.Certificate.GramRows
end OAI
