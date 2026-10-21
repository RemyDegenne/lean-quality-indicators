namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical21045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21045 raw21045Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw21045 raw21045Labels = mixedMoment B raw21045step0 raw21045step0Labels := by
      have hz : ∀ j, raw21045 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21045step0 = (fun i j => raw21045 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21045step0 raw21045; decide +kernel
      have hl : raw21045step0Labels = raw21045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21045 raw21045Labels permutation265 hz
    _ = mixedMoment B node2705 node2705Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
