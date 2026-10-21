namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem originalBlockEval40 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock40 x =
      Integer.Sparse.eval keyPolynomialBlock40 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck40, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics
end OAI
