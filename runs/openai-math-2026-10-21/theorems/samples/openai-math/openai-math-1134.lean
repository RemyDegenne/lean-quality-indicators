namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24330 raw24330Labels = mixedMoment B node4547 node4547Labels := by
  calc
    mixedMoment B raw24330 raw24330Labels = mixedMoment B raw24330step0 raw24330step0Labels := by
      have hz : ∀ j, raw24330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24330step0 = (fun i j => raw24330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24330step0 raw24330; decide +kernel
      have hl : raw24330step0Labels = raw24330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24330 raw24330Labels permutation346 hz
    mixedMoment B raw24330step0 raw24330step0Labels = mixedMoment B raw24330step1 raw24330step1Labels := by
      have ha : raw24330step1 = (fun i j => raw24330step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24330step1 raw24330step0; decide +kernel
      have hl : raw24330step1Labels = raw24330step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24330step0 raw24330step0Labels permutation32 permutation3
    mixedMoment B raw24330step1 raw24330step1Labels = mixedMoment B raw24330step2 raw24330step2Labels := by
      have ha : raw24330step2 = raw24330step1 := by apply Matrix.ext; unfold raw24330step2 raw24330step1; decide +kernel
      have hl : raw24330step1Labels = labelEmbedding6 ∘ raw24330step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24330step1 raw24330step1Labels raw24330step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4547 node4547Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
