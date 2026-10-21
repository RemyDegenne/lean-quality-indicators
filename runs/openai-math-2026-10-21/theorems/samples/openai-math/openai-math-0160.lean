namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical26332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26332 raw26332Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw26332 raw26332Labels = mixedMoment B raw26332step0 raw26332step0Labels := by
      have hz : ∀ j, raw26332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26332step0 = (fun i j => raw26332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26332step0 raw26332; decide +kernel
      have hl : raw26332step0Labels = raw26332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26332 raw26332Labels permutation346 hz
    mixedMoment B raw26332step0 raw26332step0Labels = mixedMoment B raw26332step1 raw26332step1Labels := by
      have ha : raw26332step1 = (fun i j => raw26332step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26332step1 raw26332step0; decide +kernel
      have hl : raw26332step1Labels = raw26332step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26332step0 raw26332step0Labels permutation44 permutation2
    _ = mixedMoment B node4265 node4265Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
