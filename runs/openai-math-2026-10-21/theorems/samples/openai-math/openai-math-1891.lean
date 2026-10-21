namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem rowSound1348 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1348 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1348, numericCheck1348, reducedZero1348 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge
end OAI
