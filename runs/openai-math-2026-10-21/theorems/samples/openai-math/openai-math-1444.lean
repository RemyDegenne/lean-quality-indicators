namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical38161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38161 raw38161Labels = mixedMoment B node536 node536Labels := by
  calc
    mixedMoment B raw38161 raw38161Labels = mixedMoment B raw38161step0 raw38161step0Labels := by
      have ha : raw38161step0 = raw38161 := by apply Matrix.ext; unfold raw38161step0 raw38161; decide +kernel
      have hl : raw38161Labels = labelEmbedding2 ∘ raw38161step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38161 raw38161Labels raw38161step0Labels labelEmbedding2 hl
    _ = mixedMoment B node536 node536Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
