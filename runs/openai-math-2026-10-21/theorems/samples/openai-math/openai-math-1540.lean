namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4795 raw4795Labels = mixedMoment B node1700 node1700Labels := by
  calc
    mixedMoment B raw4795 raw4795Labels = mixedMoment B raw4795step0 raw4795step0Labels := by
      have hz : ∀ j, raw4795 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw4795step0 = (fun i j => raw4795 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw4795step0 raw4795; decide +kernel
      have hl : raw4795step0Labels = raw4795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4795 raw4795Labels permutation265 hz
    mixedMoment B raw4795step0 raw4795step0Labels = mixedMoment B raw4795step1 raw4795step1Labels := by
      have ha : raw4795step1 = (fun i j => raw4795step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4795step1 raw4795step0; decide +kernel
      have hl : raw4795step1Labels = raw4795step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4795step0 raw4795step0Labels permutation137 permutation7
    mixedMoment B raw4795step1 raw4795step1Labels = mixedMoment B raw4795step2 raw4795step2Labels := by
      have ha : raw4795step2 = -raw4795step1 := by apply Matrix.ext; change ∀ i j, raw4795step2 i j = -(raw4795step1 i j); unfold raw4795step2 raw4795step1; decide +kernel
      have hl : raw4795step2Labels = raw4795step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4795step2 raw4795step2Labels = mixedMoment B raw4795step3 raw4795step3Labels := by
      have ha : raw4795step3 = raw4795step2 := by apply Matrix.ext; unfold raw4795step3 raw4795step2; decide +kernel
      have hl : raw4795step2Labels = labelEmbedding1 ∘ raw4795step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4795step2 raw4795step2Labels raw4795step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1700 node1700Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
