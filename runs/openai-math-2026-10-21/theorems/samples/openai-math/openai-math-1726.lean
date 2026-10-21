namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval7310 (x : Key → ℝ) : Integer.Sparse.eval row7310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7310, Integer.Sparse.eval_collectBalanced, rawRowCheck7310]

end MUB6.Certificate.GramRows
end OAI
