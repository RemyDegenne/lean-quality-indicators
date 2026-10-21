namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound5131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node5131 node5131Labels = Sparse.eval nodeValue5131 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 5131) = mixedMoment B node5131 node5131Labels := rfl
  simpa [nodeValue5131, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics
end OAI
