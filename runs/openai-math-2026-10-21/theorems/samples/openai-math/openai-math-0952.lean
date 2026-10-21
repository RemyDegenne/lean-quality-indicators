namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem rowSound522 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row522 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck522, numericCheck522, reducedZero522 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge
end OAI
