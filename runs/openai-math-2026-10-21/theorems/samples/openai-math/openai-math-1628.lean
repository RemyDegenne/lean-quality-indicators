namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1739 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1739 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1739 (originalVector B) := by
  rw [reducedMerge1739Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1737 B hB hF, reducedMergeEval1738 B hB hF]
  rw [originalMerge1739, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics
end OAI
