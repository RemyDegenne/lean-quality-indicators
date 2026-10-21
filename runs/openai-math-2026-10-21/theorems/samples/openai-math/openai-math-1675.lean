namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem rowSound1310 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1310 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1310, numericCheck1310, reducedZero1310 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge
end OAI
