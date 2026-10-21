namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32692 raw32692Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw32692 raw32692Labels = mixedMoment B raw32692step0 raw32692step0Labels := by
      have hz : ∀ j, raw32692 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32692step0 = (fun i j => raw32692 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32692step0 raw32692; decide +kernel
      have hl : raw32692step0Labels = raw32692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32692 raw32692Labels permutation346 hz
    mixedMoment B raw32692step0 raw32692step0Labels = mixedMoment B raw32692step1 raw32692step1Labels := by
      have ha : raw32692step1 = (fun i j => raw32692step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32692step1 raw32692step0; decide +kernel
      have hl : raw32692step1Labels = raw32692step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32692step0 raw32692step0Labels permutation33 permutation3
    mixedMoment B raw32692step1 raw32692step1Labels = mixedMoment B raw32692step2 raw32692step2Labels := by
      have ha : raw32692step2 = raw32692step1 := by apply Matrix.ext; unfold raw32692step2 raw32692step1; decide +kernel
      have hl : raw32692step1Labels = labelEmbedding6 ∘ raw32692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32692step1 raw32692step1Labels raw32692step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
