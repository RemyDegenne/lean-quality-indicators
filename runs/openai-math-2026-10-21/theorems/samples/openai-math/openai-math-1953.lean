namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical2979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2979 raw2979Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw2979 raw2979Labels = mixedMoment B raw2979step0 raw2979step0Labels := by
      have hz : ∀ j, raw2979 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2979step0 = (fun i j => raw2979 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2979step0 raw2979; decide +kernel
      have hl : raw2979step0Labels = raw2979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2979 raw2979Labels permutation265 hz
    mixedMoment B raw2979step0 raw2979step0Labels = mixedMoment B raw2979step1 raw2979step1Labels := by
      have ha : raw2979step1 = (fun i j => raw2979step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2979step1 raw2979step0; decide +kernel
      have hl : raw2979step1Labels = raw2979step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2979step0 raw2979step0Labels permutation38 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
