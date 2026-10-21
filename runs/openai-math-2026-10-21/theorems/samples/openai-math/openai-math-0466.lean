namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical37242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37242 raw37242Labels = mixedMoment B node4073 node4073Labels := by
  calc
    mixedMoment B raw37242 raw37242Labels = mixedMoment B raw37242step0 raw37242step0Labels := by
      have hz : ∀ i, raw37242 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37242step0 = (fun i j => raw37242 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37242step0 raw37242; decide +kernel
      have hl : raw37242step0Labels = (fun j => raw37242Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37242 raw37242Labels permutation6 hz
    mixedMoment B raw37242step0 raw37242step0Labels = mixedMoment B raw37242step1 raw37242step1Labels := by
      have ha : raw37242step1 = (fun i j => raw37242step0 (permutation266 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37242step1 raw37242step0; decide +kernel
      have hl : raw37242step1Labels = raw37242step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37242step0 raw37242step0Labels permutation266 permutation0
    _ = mixedMoment B node4073 node4073Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
