namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29991 raw29991Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw29991 raw29991Labels = mixedMoment B raw29991step0 raw29991step0Labels := by
      have hz : ∀ j, raw29991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29991step0 = (fun i j => raw29991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29991step0 raw29991; decide +kernel
      have hl : raw29991step0Labels = raw29991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29991 raw29991Labels permutation346 hz
    mixedMoment B raw29991step0 raw29991step0Labels = mixedMoment B raw29991step1 raw29991step1Labels := by
      have ha : raw29991step1 = (fun i j => raw29991step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29991step1 raw29991step0; decide +kernel
      have hl : raw29991step1Labels = raw29991step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29991step0 raw29991step0Labels permutation36 permutation3
    mixedMoment B raw29991step1 raw29991step1Labels = mixedMoment B raw29991step2 raw29991step2Labels := by
      have ha : raw29991step2 = raw29991step1 := by apply Matrix.ext; unfold raw29991step2 raw29991step1; decide +kernel
      have hl : raw29991step1Labels = labelEmbedding6 ∘ raw29991step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29991step1 raw29991step1Labels raw29991step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
