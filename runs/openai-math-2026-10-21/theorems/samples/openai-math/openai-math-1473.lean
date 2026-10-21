namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1656 node1656Labels = Sparse.eval nodeValue1656 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1656) = mixedMoment B node1656 node1656Labels := rfl
  simpa [nodeValue1656, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics
end OAI
