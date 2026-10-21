namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1543 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1543) =
      Integer.Sparse.eval keyMomentRow1543 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1543).leftCharge (GramAssembly.key 1543).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3706) := by
    have ha : gramCharges (GramAssembly.key 1543).leftCharge (GramAssembly.key 1543).rightCharge = raw40961 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40961Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40961 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1543).leftCharge (GramAssembly.key 1543).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1543, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics
end OAI
