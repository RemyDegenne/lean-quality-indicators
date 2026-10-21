namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40301 raw40301Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw40301 raw40301Labels = mixedMoment B raw40301step0 raw40301step0Labels := by
      have hz : ∀ j, raw40301 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40301step0 = (fun i j => raw40301 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40301step0 raw40301; decide +kernel
      have hl : raw40301step0Labels = raw40301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40301 raw40301Labels permutation265 hz
    mixedMoment B raw40301step0 raw40301step0Labels = mixedMoment B raw40301step1 raw40301step1Labels := by
      have ha : raw40301step1 = (fun i j => raw40301step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40301step1 raw40301step0; decide +kernel
      have hl : raw40301step1Labels = raw40301step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40301step0 raw40301step0Labels permutation32 permutation3
    _ = mixedMoment B node2263 node2263Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
