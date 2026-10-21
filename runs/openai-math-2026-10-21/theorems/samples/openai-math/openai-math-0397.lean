namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3636 node3636Labels = Sparse.eval nodeValue3636 (mixedVector B) := by
  simpa only [nodeValue3636, Sparse.eval_nil] using zero3636 B _hB _hF

end MUB6.Certificate.MixedSemantics
end OAI
