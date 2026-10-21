namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32780 raw32780Labels = mixedMoment B node2659 node2659Labels := by
  calc
    mixedMoment B raw32780 raw32780Labels = mixedMoment B raw32780step0 raw32780step0Labels := by
      have hz : ∀ j, raw32780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32780step0 = (fun i j => raw32780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32780step0 raw32780; decide +kernel
      have hl : raw32780step0Labels = raw32780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32780 raw32780Labels permutation346 hz
    mixedMoment B raw32780step0 raw32780step0Labels = mixedMoment B raw32780step1 raw32780step1Labels := by
      have ha : raw32780step1 = (fun i j => raw32780step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32780step1 raw32780step0; decide +kernel
      have hl : raw32780step1Labels = raw32780step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32780step0 raw32780step0Labels permutation126 permutation5
    mixedMoment B raw32780step1 raw32780step1Labels = mixedMoment B raw32780step2 raw32780step2Labels := by
      have ha : raw32780step2 = raw32780step1 := by apply Matrix.ext; unfold raw32780step2 raw32780step1; decide +kernel
      have hl : raw32780step1Labels = labelEmbedding1 ∘ raw32780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32780step1 raw32780step1Labels raw32780step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2659 node2659Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
