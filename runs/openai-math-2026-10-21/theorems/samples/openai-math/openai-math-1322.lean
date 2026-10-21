namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5083 node5083Labels = Sparse.eval nodeValue5083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5083) = mixedMoment B node5083 node5083Labels := rfl
  simpa [nodeValue5083, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics
end OAI
