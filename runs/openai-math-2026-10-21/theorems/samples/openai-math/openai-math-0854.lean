namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10613 raw10613Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw10613 raw10613Labels = mixedMoment B raw10613step0 raw10613step0Labels := by
      have hz : ∀ j, raw10613 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10613step0 = (fun i j => raw10613 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10613step0 raw10613; decide +kernel
      have hl : raw10613step0Labels = raw10613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10613 raw10613Labels permutation265 hz
    mixedMoment B raw10613step0 raw10613step0Labels = mixedMoment B raw10613step1 raw10613step1Labels := by
      have ha : raw10613step1 = (fun i j => raw10613step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10613step1 raw10613step0; decide +kernel
      have hl : raw10613step1Labels = raw10613step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10613step0 raw10613step0Labels permutation139 permutation6
    _ = mixedMoment B node3089 node3089Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
