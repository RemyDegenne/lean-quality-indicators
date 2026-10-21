namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval684 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge684 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge684 (originalVector B) := by
  rw [reducedMerge684Check, Integer.Sparse.eval_mergeBy, reducedMergeEval669 B hB hF, reducedMergeEval683 B hB hF]
  rw [originalMerge684, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics
end OAI
