namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14434 raw14434Labels = mixedMoment B node1923 node1923Labels := by
  calc
    mixedMoment B raw14434 raw14434Labels = mixedMoment B raw14434step0 raw14434step0Labels := by
      have ha : raw14434step0 = (fun i j => raw14434 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14434step0 raw14434; decide +kernel
      have hl : raw14434step0Labels = raw14434Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14434 raw14434Labels permutation686 permutation3
    mixedMoment B raw14434step0 raw14434step0Labels = mixedMoment B raw14434step1 raw14434step1Labels := by
      have ha : raw14434step1 = -raw14434step0 := by apply Matrix.ext; change ∀ i j, raw14434step1 i j = -(raw14434step0 i j); unfold raw14434step1 raw14434step0; decide +kernel
      have hl : raw14434step1Labels = raw14434step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1923 node1923Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
