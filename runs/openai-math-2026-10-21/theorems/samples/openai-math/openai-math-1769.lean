namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1206 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1206 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1206 (originalVector B) := by
  rw [reducedMerge1206Check, Integer.Sparse.eval_mergeBy, reducedTermEval1210 B hB hF, reducedTermEval1211 B hB hF]
  rw [originalMerge1206, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics
end OAI
