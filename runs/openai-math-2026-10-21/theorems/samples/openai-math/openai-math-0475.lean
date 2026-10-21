namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval1790 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm1790 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm1790 (originalVector B) := by
  rw [reducedTermArithmetic1790, ← sound5185 B hB hF]
  change (9726337145084313600000 : ℝ) * mixedMoment B node5185 node5185Labels =
    (37623398400 : ℝ) * ((258518304000 : ℝ) * mixedMoment B node5185 node5185Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics
end OAI
