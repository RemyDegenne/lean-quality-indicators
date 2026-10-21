namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20668 raw20668Labels = mixedMoment B node4531 node4531Labels := by
  calc
    mixedMoment B raw20668 raw20668Labels = mixedMoment B raw20668step0 raw20668step0Labels := by
      have hz : ∀ j, raw20668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20668step0 = (fun i j => raw20668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20668step0 raw20668; decide +kernel
      have hl : raw20668step0Labels = raw20668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20668 raw20668Labels permutation346 hz
    mixedMoment B raw20668step0 raw20668step0Labels = mixedMoment B raw20668step1 raw20668step1Labels := by
      have ha : raw20668step1 = (fun i j => raw20668step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20668step1 raw20668step0; decide +kernel
      have hl : raw20668step1Labels = raw20668step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20668step0 raw20668step0Labels permutation151 permutation2
    mixedMoment B raw20668step1 raw20668step1Labels = mixedMoment B raw20668step2 raw20668step2Labels := by
      have ha : raw20668step2 = -raw20668step1 := by apply Matrix.ext; change ∀ i j, raw20668step2 i j = -(raw20668step1 i j); unfold raw20668step2 raw20668step1; decide +kernel
      have hl : raw20668step2Labels = raw20668step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4531 node4531Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
