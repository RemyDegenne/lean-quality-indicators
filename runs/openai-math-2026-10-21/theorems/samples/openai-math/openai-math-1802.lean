namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero203 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource203 (mixedVector B) = 0 := by
  have h1283 : mixedVector B (Sum.inr 1283) = Sparse.eval nodeValue1283 (mixedVector B) := by
    change mixedMoment B node1283 node1283Labels = _
    exact sound1283 B hB hF
  have h2582 : mixedVector B (Sum.inr 2582) = Sparse.eval nodeValue2582 (mixedVector B) := by
    change mixedMoment B node2582 node2582Labels = _
    exact sound2582 B hB hF
  have h2651 : mixedVector B (Sum.inr 2651) = Sparse.eval nodeValue2651 (mixedVector B) := by
    change mixedMoment B node2651 node2651Labels = _
    exact sound2651 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm238, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1283, h2582, h2651, h2774, h2777, h4092, reducedSource203] using sourceEq238 B hB

end MUB6.Certificate.MixedSourceBridge
end OAI
