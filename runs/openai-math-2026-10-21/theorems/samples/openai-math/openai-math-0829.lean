namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31557 raw31557Labels = mixedMoment B node2057 node2057Labels := by
  calc
    mixedMoment B raw31557 raw31557Labels = mixedMoment B raw31557step0 raw31557step0Labels := by
      have hz : ∀ j, raw31557 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31557step0 = (fun i j => raw31557 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31557step0 raw31557; decide +kernel
      have hl : raw31557step0Labels = raw31557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31557 raw31557Labels permutation434 hz
    mixedMoment B raw31557step0 raw31557step0Labels = mixedMoment B raw31557step1 raw31557step1Labels := by
      have ha : raw31557step1 = (fun i j => raw31557step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31557step1 raw31557step0; decide +kernel
      have hl : raw31557step1Labels = raw31557step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31557step0 raw31557step0Labels permutation33 permutation2
    _ = mixedMoment B node2057 node2057Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
