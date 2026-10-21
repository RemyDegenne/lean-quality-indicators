namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41812 raw41812Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw41812 raw41812Labels = mixedMoment B raw41812step0 raw41812step0Labels := by
      have hz : ∀ j, raw41812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41812step0 = (fun i j => raw41812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41812step0 raw41812; decide +kernel
      have hl : raw41812step0Labels = raw41812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41812 raw41812Labels permutation346 hz
    mixedMoment B raw41812step0 raw41812step0Labels = mixedMoment B raw41812step1 raw41812step1Labels := by
      have ha : raw41812step1 = (fun i j => raw41812step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41812step1 raw41812step0; decide +kernel
      have hl : raw41812step1Labels = raw41812step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41812step0 raw41812step0Labels permutation38 permutation2
    mixedMoment B raw41812step1 raw41812step1Labels = mixedMoment B raw41812step2 raw41812step2Labels := by
      have ha : raw41812step2 = raw41812step1 := by apply Matrix.ext; unfold raw41812step2 raw41812step1; decide +kernel
      have hl : raw41812step1Labels = labelEmbedding1 ∘ raw41812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41812step1 raw41812step1Labels raw41812step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
