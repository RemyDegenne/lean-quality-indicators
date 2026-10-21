namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical36125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36125 raw36125Labels = mixedMoment B node4767 node4767Labels := by
  calc
    mixedMoment B raw36125 raw36125Labels = mixedMoment B raw36125step0 raw36125step0Labels := by
      have ha : raw36125step0 = (fun i j => raw36125 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36125step0 raw36125; decide +kernel
      have hl : raw36125step0Labels = raw36125Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36125 raw36125Labels permutation663 permutation3
    mixedMoment B raw36125step0 raw36125step0Labels = mixedMoment B raw36125step1 raw36125step1Labels := by
      have ha : raw36125step1 = -raw36125step0 := by apply Matrix.ext; change ∀ i j, raw36125step1 i j = -(raw36125step0 i j); unfold raw36125step1 raw36125step0; decide +kernel
      have hl : raw36125step1Labels = raw36125step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36125step1 raw36125step1Labels = mixedMoment B raw36125step2 raw36125step2Labels := by
      have ha : raw36125step2 = raw36125step1 := by apply Matrix.ext; unfold raw36125step2 raw36125step1; decide +kernel
      have hl : raw36125step1Labels = labelEmbedding6 ∘ raw36125step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36125step1 raw36125step1Labels raw36125step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4767 node4767Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
