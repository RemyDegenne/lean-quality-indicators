namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node119 node119Labels = Sparse.eval nodeValue119 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue119 (familyPairVector B) := singlePair119 B _hB
    _ = _ := by norm_num [singlePairValue119, nodeValue119, Sparse.eval, mixedVector]; ring

end MUB6.Certificate.MixedSemantics
end OAI
