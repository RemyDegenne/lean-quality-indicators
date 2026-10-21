namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment594 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 594) =
      Integer.Sparse.eval keyMomentRow594 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 594).leftCharge (GramAssembly.key 594).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 121) := by
    have ha : gramCharges (GramAssembly.key 594).leftCharge (GramAssembly.key 594).rightCharge = raw40042 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40042Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40042 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 594).leftCharge (GramAssembly.key 594).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow594, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics
end OAI
