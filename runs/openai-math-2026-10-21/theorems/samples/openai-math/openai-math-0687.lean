namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21265 raw21265Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw21265 raw21265Labels = mixedMoment B raw21265step0 raw21265step0Labels := by
      have hz : ∀ j, raw21265 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21265step0 = (fun i j => raw21265 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21265step0 raw21265; decide +kernel
      have hl : raw21265step0Labels = raw21265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21265 raw21265Labels permutation346 hz
    mixedMoment B raw21265step0 raw21265step0Labels = mixedMoment B raw21265step1 raw21265step1Labels := by
      have ha : raw21265step1 = (fun i j => raw21265step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21265step1 raw21265step0; decide +kernel
      have hl : raw21265step1Labels = raw21265step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21265step0 raw21265step0Labels permutation38 permutation3
    _ = mixedMoment B node2485 node2485Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
