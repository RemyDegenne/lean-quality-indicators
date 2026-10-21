namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical10078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10078 raw10078Labels = mixedMoment B node2569 node2569Labels := by
  calc
    mixedMoment B raw10078 raw10078Labels = mixedMoment B raw10078step0 raw10078step0Labels := by
      have hz : ∀ j, raw10078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10078step0 = (fun i j => raw10078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10078step0 raw10078; decide +kernel
      have hl : raw10078step0Labels = raw10078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10078 raw10078Labels permutation346 hz
    mixedMoment B raw10078step0 raw10078step0Labels = mixedMoment B raw10078step1 raw10078step1Labels := by
      have ha : raw10078step1 = (fun i j => raw10078step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10078step1 raw10078step0; decide +kernel
      have hl : raw10078step1Labels = raw10078step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10078step0 raw10078step0Labels permutation151 permutation2
    mixedMoment B raw10078step1 raw10078step1Labels = mixedMoment B raw10078step2 raw10078step2Labels := by
      have ha : raw10078step2 = -raw10078step1 := by apply Matrix.ext; change ∀ i j, raw10078step2 i j = -(raw10078step1 i j); unfold raw10078step2 raw10078step1; decide +kernel
      have hl : raw10078step2Labels = raw10078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2569 node2569Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
