namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval628 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge628 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge628 (originalVector B) := by
  rw [reducedMerge628Check, Integer.Sparse.eval_mergeBy, reducedTermEval632 B hB hF, reducedTermEval633 B hB hF]
  rw [originalMerge628, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics
end OAI
