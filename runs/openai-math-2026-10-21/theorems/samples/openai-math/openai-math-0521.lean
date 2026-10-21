namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1856 node1856Labels = Sparse.eval nodeValue1856 (mixedVector B) := by
  simpa only [nodeValue1856, Sparse.eval_nil] using zero1856 B _hB _hF

end MUB6.Certificate.MixedSemantics
end OAI
