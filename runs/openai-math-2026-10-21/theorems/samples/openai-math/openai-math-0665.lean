namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8057 raw8057Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw8057 raw8057Labels = mixedMoment B raw8057step0 raw8057step0Labels := by
      have hz : ∀ j, raw8057 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8057step0 = (fun i j => raw8057 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8057step0 raw8057; decide +kernel
      have hl : raw8057step0Labels = raw8057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8057 raw8057Labels permutation346 hz
    mixedMoment B raw8057step0 raw8057step0Labels = mixedMoment B raw8057step1 raw8057step1Labels := by
      have hz : ∀ j, raw8057step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8057step1 = (fun i j => raw8057step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8057step1 raw8057step0; decide +kernel
      have hl : raw8057step1Labels = raw8057step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8057step0 raw8057step0Labels permutation56 hz
    mixedMoment B raw8057step1 raw8057step1Labels = mixedMoment B raw8057step2 raw8057step2Labels := by
      have ha : raw8057step2 = (fun i j => raw8057step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8057step2 raw8057step1; decide +kernel
      have hl : raw8057step2Labels = raw8057step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8057step1 raw8057step1Labels permutation8 permutation3
    _ = mixedMoment B node1046 node1046Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
