namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24155 raw24155Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw24155 raw24155Labels = mixedMoment B raw24155step0 raw24155step0Labels := by
      have hz : ∀ j, raw24155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24155step0 = (fun i j => raw24155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24155step0 raw24155; decide +kernel
      have hl : raw24155step0Labels = raw24155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24155 raw24155Labels permutation346 hz
    mixedMoment B raw24155step0 raw24155step0Labels = mixedMoment B raw24155step1 raw24155step1Labels := by
      have hz : ∀ j, raw24155step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24155step1 = (fun i j => raw24155step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24155step1 raw24155step0; decide +kernel
      have hl : raw24155step1Labels = raw24155step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24155step0 raw24155step0Labels permutation56 hz
    mixedMoment B raw24155step1 raw24155step1Labels = mixedMoment B raw24155step2 raw24155step2Labels := by
      have ha : raw24155step2 = (fun i j => raw24155step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24155step2 raw24155step1; decide +kernel
      have hl : raw24155step2Labels = raw24155step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24155step1 raw24155step1Labels permutation8 permutation7
    mixedMoment B raw24155step2 raw24155step2Labels = mixedMoment B raw24155step3 raw24155step3Labels := by
      have ha : raw24155step3 = raw24155step2 := by apply Matrix.ext; unfold raw24155step3 raw24155step2; decide +kernel
      have hl : raw24155step2Labels = labelEmbedding10 ∘ raw24155step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24155step2 raw24155step2Labels raw24155step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
