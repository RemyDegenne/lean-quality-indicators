namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1625 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1625 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1625 (originalVector B) := by
  rw [reducedMerge1625Check, Integer.Sparse.eval_mergeBy, reducedTermEval1632 B hB hF, reducedTermEval1633 B hB hF]
  rw [originalMerge1625, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics
end OAI
