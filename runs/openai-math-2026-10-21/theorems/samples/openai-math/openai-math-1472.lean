namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical25967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25967 raw25967Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw25967 raw25967Labels = mixedMoment B raw25967step0 raw25967step0Labels := by
      have hz : ∀ j, raw25967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25967step0 = (fun i j => raw25967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25967step0 raw25967; decide +kernel
      have hl : raw25967step0Labels = raw25967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25967 raw25967Labels permutation346 hz
    mixedMoment B raw25967step0 raw25967step0Labels = mixedMoment B raw25967step1 raw25967step1Labels := by
      have hz : ∀ j, raw25967step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25967step1 = (fun i j => raw25967step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25967step1 raw25967step0; decide +kernel
      have hl : raw25967step1Labels = raw25967step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25967step0 raw25967step0Labels permutation56 hz
    mixedMoment B raw25967step1 raw25967step1Labels = mixedMoment B raw25967step2 raw25967step2Labels := by
      have ha : raw25967step2 = (fun i j => raw25967step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25967step2 raw25967step1; decide +kernel
      have hl : raw25967step2Labels = raw25967step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25967step1 raw25967step1Labels permutation12 permutation3
    _ = mixedMoment B node1436 node1436Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
