namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19814 raw19814Labels = mixedMoment B node1456 node1456Labels := by
  calc
    mixedMoment B raw19814 raw19814Labels = mixedMoment B raw19814step0 raw19814step0Labels := by
      have hz : ∀ j, raw19814 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19814step0 = (fun i j => raw19814 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19814step0 raw19814; decide +kernel
      have hl : raw19814step0Labels = raw19814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19814 raw19814Labels permutation520 hz
    mixedMoment B raw19814step0 raw19814step0Labels = mixedMoment B raw19814step1 raw19814step1Labels := by
      have hz : ∀ j, raw19814step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19814step1 = (fun i j => raw19814step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19814step1 raw19814step0; decide +kernel
      have hl : raw19814step1Labels = raw19814step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19814step0 raw19814step0Labels permutation104 hz
    mixedMoment B raw19814step1 raw19814step1Labels = mixedMoment B raw19814step2 raw19814step2Labels := by
      have hz : ∀ j, raw19814step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19814step2 = (fun i j => raw19814step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19814step2 raw19814step1; decide +kernel
      have hl : raw19814step2Labels = raw19814step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19814step1 raw19814step1Labels permutation20 hz
    mixedMoment B raw19814step2 raw19814step2Labels = mixedMoment B raw19814step3 raw19814step3Labels := by
      have hz : ∀ j, raw19814step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19814step3 = (fun i j => raw19814step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19814step3 raw19814step2; decide +kernel
      have hl : raw19814step3Labels = raw19814step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19814step2 raw19814step2Labels permutation4 hz
    mixedMoment B raw19814step3 raw19814step3Labels = mixedMoment B raw19814step4 raw19814step4Labels := by
      have ha : raw19814step4 = (fun i j => raw19814step3 (permutation0 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19814step4 raw19814step3; decide +kernel
      have hl : raw19814step4Labels = raw19814step3Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19814step3 raw19814step3Labels permutation0 permutation7
    mixedMoment B raw19814step4 raw19814step4Labels = mixedMoment B raw19814step5 raw19814step5Labels := by
      have ha : raw19814step5 = raw19814step4 := by apply Matrix.ext; unfold raw19814step5 raw19814step4; decide +kernel
      have hl : raw19814step4Labels = labelEmbedding1 ∘ raw19814step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19814step4 raw19814step4Labels raw19814step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1456 node1456Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
