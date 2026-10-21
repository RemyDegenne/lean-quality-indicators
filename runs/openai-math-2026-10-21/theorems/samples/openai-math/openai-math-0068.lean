namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22866 raw22866Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw22866 raw22866Labels = mixedMoment B raw22866step0 raw22866step0Labels := by
      have hz : ∀ j, raw22866 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22866step0 = (fun i j => raw22866 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22866step0 raw22866; decide +kernel
      have hl : raw22866step0Labels = raw22866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22866 raw22866Labels permutation265 hz
    mixedMoment B raw22866step0 raw22866step0Labels = mixedMoment B raw22866step1 raw22866step1Labels := by
      have ha : raw22866step1 = (fun i j => raw22866step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22866step1 raw22866step0; decide +kernel
      have hl : raw22866step1Labels = raw22866step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22866step0 raw22866step0Labels permutation33 permutation2
    _ = mixedMoment B node2467 node2467Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
