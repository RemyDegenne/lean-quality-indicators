namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node617 node617Labels = Sparse.eval nodeValue617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 617) = mixedMoment B node617 node617Labels := rfl
  simpa [nodeValue617, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics
end OAI
