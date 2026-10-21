namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical37272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37272 raw37272Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw37272 raw37272Labels = mixedMoment B raw37272step0 raw37272step0Labels := by
      have ha : raw37272step0 = (fun i j => raw37272 (permutation654 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37272step0 raw37272; decide +kernel
      have hl : raw37272step0Labels = raw37272Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37272 raw37272Labels permutation654 permutation2
    mixedMoment B raw37272step0 raw37272step0Labels = mixedMoment B raw37272step1 raw37272step1Labels := by
      have ha : raw37272step1 = -raw37272step0 := by apply Matrix.ext; change ∀ i j, raw37272step1 i j = -(raw37272step0 i j); unfold raw37272step1 raw37272step0; decide +kernel
      have hl : raw37272step1Labels = raw37272step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5406 node5406Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
