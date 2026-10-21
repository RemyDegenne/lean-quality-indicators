namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical38411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38411 raw38411Labels = mixedMoment B node872 node872Labels := by
  calc
    mixedMoment B raw38411 raw38411Labels = mixedMoment B raw38411step0 raw38411step0Labels := by
      have ha : raw38411step0 = raw38411 := by apply Matrix.ext; unfold raw38411step0 raw38411; decide +kernel
      have hl : raw38411Labels = labelEmbedding2 ∘ raw38411step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38411 raw38411Labels raw38411step0Labels labelEmbedding2 hl
    _ = mixedMoment B node872 node872Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
