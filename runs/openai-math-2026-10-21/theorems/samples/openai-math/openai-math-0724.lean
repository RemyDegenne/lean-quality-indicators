namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22053 raw22053Labels = mixedMoment B node823 node823Labels := by
  calc
    mixedMoment B raw22053 raw22053Labels = mixedMoment B raw22053step0 raw22053step0Labels := by
      have hz : ∀ j, raw22053 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22053step0 = (fun i j => raw22053 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22053step0 raw22053; decide +kernel
      have hl : raw22053step0Labels = raw22053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22053 raw22053Labels permutation434 hz
    _ = mixedMoment B node823 node823Labels := by rfl

end MUB6.Certificate.MixedSemantics
end OAI
