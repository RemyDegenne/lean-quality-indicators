namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem rowSound1645 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1645 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1645, numericCheck1645, reducedZero1645 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge
end OAI
