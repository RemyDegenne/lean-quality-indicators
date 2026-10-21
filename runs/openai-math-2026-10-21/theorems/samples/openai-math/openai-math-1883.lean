namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical19350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19350 raw19350Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw19350 raw19350Labels = mixedMoment B raw19350step0 raw19350step0Labels := by
      have ha : raw19350step0 = (fun i j => raw19350 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19350step0 raw19350; decide +kernel
      have hl : raw19350step0Labels = raw19350Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19350 raw19350Labels permutation155 permutation2
    _ = mixedMoment B node5424 node5424Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
