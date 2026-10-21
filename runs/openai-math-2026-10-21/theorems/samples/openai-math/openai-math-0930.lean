namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical33575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33575 raw33575Labels = mixedMoment B node4696 node4696Labels := by
  calc
    mixedMoment B raw33575 raw33575Labels = mixedMoment B raw33575step0 raw33575step0Labels := by
      have ha : raw33575step0 = (fun i j => raw33575 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33575step0 raw33575; decide +kernel
      have hl : raw33575step0Labels = raw33575Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33575 raw33575Labels permutation154 permutation2
    _ = mixedMoment B node4696 node4696Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
