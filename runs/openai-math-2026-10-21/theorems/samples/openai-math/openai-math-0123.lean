namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19146 raw19146Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19146 raw19146Labels = mixedMoment B raw19146step0 raw19146step0Labels := by
      have ha : raw19146step0 = (fun i j => raw19146 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19146step0 raw19146; decide +kernel
      have hl : raw19146step0Labels = raw19146Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19146 raw19146Labels permutation176 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
