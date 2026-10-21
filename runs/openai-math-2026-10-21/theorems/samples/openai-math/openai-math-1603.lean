namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29932 raw29932Labels = mixedMoment B node2802 node2802Labels := by
  calc
    mixedMoment B raw29932 raw29932Labels = mixedMoment B raw29932step0 raw29932step0Labels := by
      have hz : ∀ j, raw29932 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29932step0 = (fun i j => raw29932 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29932step0 raw29932; decide +kernel
      have hl : raw29932step0Labels = raw29932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29932 raw29932Labels permutation434 hz
    _ = mixedMoment B node2802 node2802Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
