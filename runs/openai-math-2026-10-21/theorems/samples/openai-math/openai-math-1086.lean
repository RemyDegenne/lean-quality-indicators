namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6110 raw6110Labels = mixedMoment B node2035 node2035Labels := by
  calc
    mixedMoment B raw6110 raw6110Labels = mixedMoment B raw6110step0 raw6110step0Labels := by
      have hz : ∀ j, raw6110 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6110step0 = (fun i j => raw6110 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6110step0 raw6110; decide +kernel
      have hl : raw6110step0Labels = raw6110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6110 raw6110Labels permutation434 hz
    mixedMoment B raw6110step0 raw6110step0Labels = mixedMoment B raw6110step1 raw6110step1Labels := by
      have ha : raw6110step1 = (fun i j => raw6110step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6110step1 raw6110step0; decide +kernel
      have hl : raw6110step1Labels = raw6110step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6110step0 raw6110step0Labels permutation36 permutation4
    mixedMoment B raw6110step1 raw6110step1Labels = mixedMoment B raw6110step2 raw6110step2Labels := by
      have ha : raw6110step2 = -raw6110step1 := by apply Matrix.ext; change ∀ i j, raw6110step2 i j = -(raw6110step1 i j); unfold raw6110step2 raw6110step1; decide +kernel
      have hl : raw6110step2Labels = raw6110step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2035 node2035Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
