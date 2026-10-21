namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16958 raw16958Labels = mixedMoment B node3882 node3882Labels := by
  calc
    mixedMoment B raw16958 raw16958Labels = mixedMoment B raw16958step0 raw16958step0Labels := by
      have ha : raw16958step0 = (fun i j => raw16958 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16958step0 raw16958; decide +kernel
      have hl : raw16958step0Labels = raw16958Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16958 raw16958Labels permutation514 permutation6
    _ = mixedMoment B node3882 node3882Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
