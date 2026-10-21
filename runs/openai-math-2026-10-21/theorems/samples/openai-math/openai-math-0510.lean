namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2717 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2717) =
      Integer.Sparse.eval keyMomentRow2717 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3463) := by
    have ha : gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge = raw42746 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42746Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42746 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5074) := by
    have ha : gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge = raw42747 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42747Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42747 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2717).leftCharge (GramAssembly.key 2717).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2717, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics
end OAI
