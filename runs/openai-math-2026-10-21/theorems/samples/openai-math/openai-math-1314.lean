namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13006 raw13006Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw13006 raw13006Labels = mixedMoment B raw13006step0 raw13006step0Labels := by
      have ha : raw13006step0 = (fun i j => raw13006 (permutation233 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13006step0 raw13006; decide +kernel
      have hl : raw13006step0Labels = raw13006Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13006 raw13006Labels permutation233 permutation3
    mixedMoment B raw13006step0 raw13006step0Labels = mixedMoment B raw13006step1 raw13006step1Labels := by
      have ha : raw13006step1 = raw13006step0 := by apply Matrix.ext; unfold raw13006step1 raw13006step0; decide +kernel
      have hl : raw13006step0Labels = labelEmbedding6 ∘ raw13006step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13006step0 raw13006step0Labels raw13006step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
