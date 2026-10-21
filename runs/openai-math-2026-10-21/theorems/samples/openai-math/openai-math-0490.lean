namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3362 raw3362Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3362 raw3362Labels = mixedMoment B raw3362step0 raw3362step0Labels := by
      have ha : raw3362step0 = (fun i j => raw3362 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3362step0 raw3362; decide +kernel
      have hl : raw3362step0Labels = raw3362Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3362 raw3362Labels permutation583 permutation3
    mixedMoment B raw3362step0 raw3362step0Labels = mixedMoment B raw3362step1 raw3362step1Labels := by
      have ha : raw3362step1 = -raw3362step0 := by apply Matrix.ext; change ∀ i j, raw3362step1 i j = -(raw3362step0 i j); unfold raw3362step1 raw3362step0; decide +kernel
      have hl : raw3362step1Labels = raw3362step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3362step1 raw3362step1Labels = mixedMoment B raw3362step2 raw3362step2Labels := by
      have ha : raw3362step2 = raw3362step1 := by apply Matrix.ext; unfold raw3362step2 raw3362step1; decide +kernel
      have hl : raw3362step1Labels = labelEmbedding6 ∘ raw3362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3362step1 raw3362step1Labels raw3362step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
