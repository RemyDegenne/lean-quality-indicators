namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval13922 (x : Key → ℝ) : Integer.Sparse.eval row13922 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![3, 0, -1, -1, 0, -1] GramFunctions.Block4.form7) x := by
  rw [rowCheck13922, Integer.Sparse.eval_collectBalanced, rawRowCheck13922]

end MUB6.Certificate.GramRows
end OAI
