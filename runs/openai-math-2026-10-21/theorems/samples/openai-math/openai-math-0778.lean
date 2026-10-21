namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17263 raw17263Labels = mixedMoment B node5419 node5419Labels := by
  calc
    mixedMoment B raw17263 raw17263Labels = mixedMoment B raw17263step0 raw17263step0Labels := by
      have ha : raw17263step0 = (fun i j => raw17263 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17263step0 raw17263; decide +kernel
      have hl : raw17263step0Labels = raw17263Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17263 raw17263Labels permutation663 permutation2
    mixedMoment B raw17263step0 raw17263step0Labels = mixedMoment B raw17263step1 raw17263step1Labels := by
      have ha : raw17263step1 = -raw17263step0 := by apply Matrix.ext; change ∀ i j, raw17263step1 i j = -(raw17263step0 i j); unfold raw17263step1 raw17263step0; decide +kernel
      have hl : raw17263step1Labels = raw17263step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5419 node5419Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
