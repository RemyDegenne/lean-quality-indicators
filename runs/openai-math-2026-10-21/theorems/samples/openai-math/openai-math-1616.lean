namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3390 raw3390Labels = mixedMoment B node5500 node5500Labels := by
  calc
    mixedMoment B raw3390 raw3390Labels = mixedMoment B raw3390step0 raw3390step0Labels := by
      have ha : raw3390step0 = (fun i j => raw3390 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3390step0 raw3390; decide +kernel
      have hl : raw3390step0Labels = raw3390Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3390 raw3390Labels permutation157 permutation2
    _ = mixedMoment B node5500 node5500Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
