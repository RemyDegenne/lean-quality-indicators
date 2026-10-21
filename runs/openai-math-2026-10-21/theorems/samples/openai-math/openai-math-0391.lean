namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical34240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34240 raw34240Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw34240 raw34240Labels = mixedMoment B raw34240step0 raw34240step0Labels := by
      have hz : ∀ j, raw34240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34240step0 = (fun i j => raw34240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34240step0 raw34240; decide +kernel
      have hl : raw34240step0Labels = raw34240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34240 raw34240Labels permutation346 hz
    mixedMoment B raw34240step0 raw34240step0Labels = mixedMoment B raw34240step1 raw34240step1Labels := by
      have ha : raw34240step1 = (fun i j => raw34240step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34240step1 raw34240step0; decide +kernel
      have hl : raw34240step1Labels = raw34240step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34240step0 raw34240step0Labels permutation34 permutation2
    _ = mixedMoment B node3392 node3392Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
