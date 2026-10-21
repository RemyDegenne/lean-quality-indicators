namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval7677 (x : Key → ℝ) : Integer.Sparse.eval row7677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -2, 0, -1] GramFunctions.Block3.form2) x := by
  rw [rowCheck7677, Integer.Sparse.eval_collectBalanced, rawRowCheck7677]

end MUB6.Certificate.GramRows
end OAI
