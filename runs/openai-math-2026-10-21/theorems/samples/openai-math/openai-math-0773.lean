namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15374 raw15374Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw15374 raw15374Labels = mixedMoment B raw15374step0 raw15374step0Labels := by
      have hz : ∀ j, raw15374 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15374step0 = (fun i j => raw15374 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15374step0 raw15374; decide +kernel
      have hl : raw15374step0Labels = raw15374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15374 raw15374Labels permutation346 hz
    mixedMoment B raw15374step0 raw15374step0Labels = mixedMoment B raw15374step1 raw15374step1Labels := by
      have ha : raw15374step1 = (fun i j => raw15374step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15374step1 raw15374step0; decide +kernel
      have hl : raw15374step1Labels = raw15374step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15374step0 raw15374step0Labels permutation146 permutation2
    mixedMoment B raw15374step1 raw15374step1Labels = mixedMoment B raw15374step2 raw15374step2Labels := by
      have ha : raw15374step2 = -raw15374step1 := by apply Matrix.ext; change ∀ i j, raw15374step2 i j = -(raw15374step1 i j); unfold raw15374step2 raw15374step1; decide +kernel
      have hl : raw15374step2Labels = raw15374step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3961 node3961Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
