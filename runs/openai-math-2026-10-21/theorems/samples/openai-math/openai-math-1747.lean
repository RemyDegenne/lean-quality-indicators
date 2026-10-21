namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24233 raw24233Labels = mixedMoment B node2960 node2960Labels := by
  calc
    mixedMoment B raw24233 raw24233Labels = mixedMoment B raw24233step0 raw24233step0Labels := by
      have hz : ∀ j, raw24233 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24233step0 = (fun i j => raw24233 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24233step0 raw24233; decide +kernel
      have hl : raw24233step0Labels = raw24233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24233 raw24233Labels permutation265 hz
    mixedMoment B raw24233step0 raw24233step0Labels = mixedMoment B raw24233step1 raw24233step1Labels := by
      have ha : raw24233step1 = (fun i j => raw24233step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24233step1 raw24233step0; decide +kernel
      have hl : raw24233step1Labels = raw24233step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24233step0 raw24233step0Labels permutation34 permutation3
    _ = mixedMoment B node2960 node2960Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
