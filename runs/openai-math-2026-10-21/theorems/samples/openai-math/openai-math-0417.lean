namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15783 raw15783Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw15783 raw15783Labels = mixedMoment B raw15783step0 raw15783step0Labels := by
      have ha : raw15783step0 = (fun i j => raw15783 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15783step0 raw15783; decide +kernel
      have hl : raw15783step0Labels = raw15783Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15783 raw15783Labels permutation686 permutation3
    mixedMoment B raw15783step0 raw15783step0Labels = mixedMoment B raw15783step1 raw15783step1Labels := by
      have ha : raw15783step1 = -raw15783step0 := by apply Matrix.ext; change ∀ i j, raw15783step1 i j = -(raw15783step0 i j); unfold raw15783step1 raw15783step0; decide +kernel
      have hl : raw15783step1Labels = raw15783step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3782 node3782Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
