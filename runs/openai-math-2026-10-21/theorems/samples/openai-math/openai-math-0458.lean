namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41044 raw41044Labels = mixedMoment B node2900 node2900Labels := by
  calc
    mixedMoment B raw41044 raw41044Labels = mixedMoment B raw41044step0 raw41044step0Labels := by
      have ha : raw41044step0 = (fun i j => raw41044 (permutation205 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41044step0 raw41044; decide +kernel
      have hl : raw41044step0Labels = raw41044Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41044 raw41044Labels permutation205 permutation6
    mixedMoment B raw41044step0 raw41044step0Labels = mixedMoment B raw41044step1 raw41044step1Labels := by
      have ha : raw41044step1 = -raw41044step0 := by apply Matrix.ext; change ∀ i j, raw41044step1 i j = -(raw41044step0 i j); unfold raw41044step1 raw41044step0; decide +kernel
      have hl : raw41044step1Labels = raw41044step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2900 node2900Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
