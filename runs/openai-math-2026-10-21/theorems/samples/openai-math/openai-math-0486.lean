namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22410 raw22410Labels = mixedMoment B node1657 node1657Labels := by
  calc
    mixedMoment B raw22410 raw22410Labels = mixedMoment B raw22410step0 raw22410step0Labels := by
      have hz : ∀ j, raw22410 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22410step0 = (fun i j => raw22410 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22410step0 raw22410; decide +kernel
      have hl : raw22410step0Labels = raw22410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22410 raw22410Labels permutation434 hz
    mixedMoment B raw22410step0 raw22410step0Labels = mixedMoment B raw22410step1 raw22410step1Labels := by
      have hz : ∀ j, raw22410step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22410step1 = (fun i j => raw22410step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22410step1 raw22410step0; decide +kernel
      have hl : raw22410step1Labels = raw22410step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22410step0 raw22410step0Labels permutation80 hz
    mixedMoment B raw22410step1 raw22410step1Labels = mixedMoment B raw22410step2 raw22410step2Labels := by
      have ha : raw22410step2 = (fun i j => raw22410step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22410step2 raw22410step1; decide +kernel
      have hl : raw22410step2Labels = raw22410step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22410step1 raw22410step1Labels permutation12 permutation2
    mixedMoment B raw22410step2 raw22410step2Labels = mixedMoment B raw22410step3 raw22410step3Labels := by
      have ha : raw22410step3 = -raw22410step2 := by apply Matrix.ext; change ∀ i j, raw22410step3 i j = -(raw22410step2 i j); unfold raw22410step3 raw22410step2; decide +kernel
      have hl : raw22410step3Labels = raw22410step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1657 node1657Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
