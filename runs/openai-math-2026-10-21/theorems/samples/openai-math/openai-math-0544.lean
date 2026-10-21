namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical37928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37928 raw37928Labels = mixedMoment B node187 node187Labels := by
  calc
    mixedMoment B raw37928 raw37928Labels = mixedMoment B raw37928step0 raw37928step0Labels := by
      have ha : raw37928step0 = (fun i j => raw37928 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37928step0 raw37928; decide +kernel
      have hl : raw37928step0Labels = raw37928Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37928 raw37928Labels permutation31 permutation3
    mixedMoment B raw37928step0 raw37928step0Labels = mixedMoment B raw37928step1 raw37928step1Labels := by
      have ha : raw37928step1 = -raw37928step0 := by apply Matrix.ext; change ∀ i j, raw37928step1 i j = -(raw37928step0 i j); unfold raw37928step1 raw37928step0; decide +kernel
      have hl : raw37928step1Labels = raw37928step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node187 node187Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
