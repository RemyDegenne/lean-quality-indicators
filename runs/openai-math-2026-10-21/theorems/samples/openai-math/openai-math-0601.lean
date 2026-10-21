namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound23 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node23 node23Labels = Sparse.eval nodeValue23 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue23 (familyPairVector B) := singlePair23 B _hB
    _ = _ := by norm_num [singlePairValue23, nodeValue23, Sparse.eval, mixedVector]; ring

end MUB6.Certificate.MixedSemantics
end OAI
