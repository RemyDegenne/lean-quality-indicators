namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1126) =
      Integer.Sparse.eval keyMomentRow1126 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1126).leftCharge (GramAssembly.key 1126).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3583) := by
    have ha : gramCharges (GramAssembly.key 1126).leftCharge (GramAssembly.key 1126).rightCharge = raw40565 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40565Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40565 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1126).leftCharge (GramAssembly.key 1126).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1126, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics
end OAI
