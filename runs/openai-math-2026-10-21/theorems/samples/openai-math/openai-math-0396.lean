namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40614 raw40614Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw40614 raw40614Labels = mixedMoment B raw40614step0 raw40614step0Labels := by
      have hz : ∀ j, raw40614 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40614step0 = (fun i j => raw40614 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40614step0 raw40614; decide +kernel
      have hl : raw40614step0Labels = raw40614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40614 raw40614Labels permutation434 hz
    mixedMoment B raw40614step0 raw40614step0Labels = mixedMoment B raw40614step1 raw40614step1Labels := by
      have hz : ∀ j, raw40614step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40614step1 = (fun i j => raw40614step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40614step1 raw40614step0; decide +kernel
      have hl : raw40614step1Labels = raw40614step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40614step0 raw40614step0Labels permutation80 hz
    mixedMoment B raw40614step1 raw40614step1Labels = mixedMoment B raw40614step2 raw40614step2Labels := by
      have ha : raw40614step2 = (fun i j => raw40614step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40614step2 raw40614step1; decide +kernel
      have hl : raw40614step2Labels = raw40614step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40614step1 raw40614step1Labels permutation26 permutation6
    _ = mixedMoment B node3052 node3052Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
