namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1737 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1737 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1737 (originalVector B) := by
  rw [reducedTermArithmetic1737, ← sound4933 B hB hF]
  change (1421670070005792768000 : ℝ) * mixedMoment B node4933 node4933Labels =
    (37623398400 : ℝ) * ((37786859520 : ℝ) * mixedMoment B node4933 node4933Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics
end OAI
