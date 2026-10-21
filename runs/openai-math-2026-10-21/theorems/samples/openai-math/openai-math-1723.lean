namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem rowSound410 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row410 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck410, numericCheck410, reducedZero410 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge
end OAI
