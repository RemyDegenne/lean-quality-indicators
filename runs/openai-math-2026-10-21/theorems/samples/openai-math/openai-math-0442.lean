namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15328 raw15328Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw15328 raw15328Labels = mixedMoment B raw15328step0 raw15328step0Labels := by
      have hz : ∀ j, raw15328 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15328step0 = (fun i j => raw15328 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15328step0 raw15328; decide +kernel
      have hl : raw15328step0Labels = raw15328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15328 raw15328Labels permutation346 hz
    mixedMoment B raw15328step0 raw15328step0Labels = mixedMoment B raw15328step1 raw15328step1Labels := by
      have ha : raw15328step1 = (fun i j => raw15328step0 (permutation122 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15328step1 raw15328step0; decide +kernel
      have hl : raw15328step1Labels = raw15328step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15328step0 raw15328step0Labels permutation122 permutation7
    mixedMoment B raw15328step1 raw15328step1Labels = mixedMoment B raw15328step2 raw15328step2Labels := by
      have ha : raw15328step2 = raw15328step1 := by apply Matrix.ext; unfold raw15328step2 raw15328step1; decide +kernel
      have hl : raw15328step1Labels = labelEmbedding1 ∘ raw15328step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15328step1 raw15328step1Labels raw15328step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3982 node3982Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
