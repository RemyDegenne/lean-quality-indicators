namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14861 raw14861Labels = mixedMoment B node3698 node3698Labels := by
  calc
    mixedMoment B raw14861 raw14861Labels = mixedMoment B raw14861step0 raw14861step0Labels := by
      have ha : raw14861step0 = (fun i j => raw14861 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14861step0 raw14861; decide +kernel
      have hl : raw14861step0Labels = raw14861Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14861 raw14861Labels permutation688 permutation3
    mixedMoment B raw14861step0 raw14861step0Labels = mixedMoment B raw14861step1 raw14861step1Labels := by
      have ha : raw14861step1 = -raw14861step0 := by apply Matrix.ext; change ∀ i j, raw14861step1 i j = -(raw14861step0 i j); unfold raw14861step1 raw14861step0; decide +kernel
      have hl : raw14861step1Labels = raw14861step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3698 node3698Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
