namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6736 raw6736Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw6736 raw6736Labels = mixedMoment B raw6736step0 raw6736step0Labels := by
      have hz : ∀ j, raw6736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6736step0 = (fun i j => raw6736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6736step0 raw6736; decide +kernel
      have hl : raw6736step0Labels = raw6736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6736 raw6736Labels permutation346 hz
    mixedMoment B raw6736step0 raw6736step0Labels = mixedMoment B raw6736step1 raw6736step1Labels := by
      have hz : ∀ j, raw6736step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6736step1 = (fun i j => raw6736step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6736step1 raw6736step0; decide +kernel
      have hl : raw6736step1Labels = raw6736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6736step0 raw6736step0Labels permutation56 hz
    mixedMoment B raw6736step1 raw6736step1Labels = mixedMoment B raw6736step2 raw6736step2Labels := by
      have ha : raw6736step2 = (fun i j => raw6736step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6736step2 raw6736step1; decide +kernel
      have hl : raw6736step2Labels = raw6736step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6736step1 raw6736step1Labels permutation8 permutation6
    _ = mixedMoment B node2774 node2774Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
