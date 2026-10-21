namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment427 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 427) =
      Integer.Sparse.eval keyMomentRow427 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 427).leftCharge (GramAssembly.key 427).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 17) := by
    have ha : gramCharges (GramAssembly.key 427).leftCharge (GramAssembly.key 427).rightCharge = raw39875 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39875Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39875 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 427).leftCharge (GramAssembly.key 427).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow427, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics
end OAI
