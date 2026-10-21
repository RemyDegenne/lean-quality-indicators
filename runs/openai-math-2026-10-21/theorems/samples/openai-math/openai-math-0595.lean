namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7015 raw7015Labels = mixedMoment B node3506 node3506Labels := by
  calc
    mixedMoment B raw7015 raw7015Labels = mixedMoment B raw7015step0 raw7015step0Labels := by
      have hz : ∀ j, raw7015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7015step0 = (fun i j => raw7015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7015step0 raw7015; decide +kernel
      have hl : raw7015step0Labels = raw7015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7015 raw7015Labels permutation346 hz
    mixedMoment B raw7015step0 raw7015step0Labels = mixedMoment B raw7015step1 raw7015step1Labels := by
      have ha : raw7015step1 = (fun i j => raw7015step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7015step1 raw7015step0; decide +kernel
      have hl : raw7015step1Labels = raw7015step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7015step0 raw7015step0Labels permutation36 permutation5
    mixedMoment B raw7015step1 raw7015step1Labels = mixedMoment B raw7015step2 raw7015step2Labels := by
      have ha : raw7015step2 = -raw7015step1 := by apply Matrix.ext; change ∀ i j, raw7015step2 i j = -(raw7015step1 i j); unfold raw7015step2 raw7015step1; decide +kernel
      have hl : raw7015step2Labels = raw7015step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7015step2 raw7015step2Labels = mixedMoment B raw7015step3 raw7015step3Labels := by
      have ha : raw7015step3 = raw7015step2 := by apply Matrix.ext; unfold raw7015step3 raw7015step2; decide +kernel
      have hl : raw7015step2Labels = labelEmbedding1 ∘ raw7015step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7015step2 raw7015step2Labels raw7015step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3506 node3506Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
