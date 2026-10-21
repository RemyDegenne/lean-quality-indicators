namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4155 node4155Labels = Sparse.eval nodeValue4155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4155) = mixedMoment B node4155 node4155Labels := rfl
  simpa [nodeValue4155, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics
end OAI
