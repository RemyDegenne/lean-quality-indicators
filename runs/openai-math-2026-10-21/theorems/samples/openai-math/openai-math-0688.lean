namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32243 raw32243Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw32243 raw32243Labels = mixedMoment B raw32243step0 raw32243step0Labels := by
      have hz : ∀ j, raw32243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32243step0 = (fun i j => raw32243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32243step0 raw32243; decide +kernel
      have hl : raw32243step0Labels = raw32243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32243 raw32243Labels permutation346 hz
    mixedMoment B raw32243step0 raw32243step0Labels = mixedMoment B raw32243step1 raw32243step1Labels := by
      have ha : raw32243step1 = (fun i j => raw32243step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32243step1 raw32243step0; decide +kernel
      have hl : raw32243step1Labels = raw32243step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32243step0 raw32243step0Labels permutation34 permutation6
    mixedMoment B raw32243step1 raw32243step1Labels = mixedMoment B raw32243step2 raw32243step2Labels := by
      have ha : raw32243step2 = raw32243step1 := by apply Matrix.ext; unfold raw32243step2 raw32243step1; decide +kernel
      have hl : raw32243step1Labels = labelEmbedding9 ∘ raw32243step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32243step1 raw32243step1Labels raw32243step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
