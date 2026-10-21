namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm835 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA835 + difference 0 1) (sourceB835 + difference 1 0) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA835 + difference 0 1) (sourceB835 + difference 1 0) sourceC835) = raw13770 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13770; decide +kernel
    rw [ha]
    exact (canonical13770 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA835 + difference 1 1) (sourceB835 + difference 1 1) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA835 + difference 1 1) (sourceB835 + difference 1 1) sourceC835) = raw13764 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13764; decide +kernel
    rw [ha]
    exact (canonical13764 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA835 + difference 2 1) (sourceB835 + difference 1 2) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2631) := by
    have ha : (tripleCharges (sourceA835 + difference 2 1) (sourceB835 + difference 1 2) sourceC835) = raw13771 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13771; decide +kernel
    rw [ha]
    exact (canonical13771 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA835 + difference 3 1) (sourceB835 + difference 1 3) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA835 + difference 3 1) (sourceB835 + difference 1 3) sourceC835) = raw13772 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13772; decide +kernel
    rw [ha]
    exact (canonical13772 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA835 + difference 4 1) (sourceB835 + difference 1 4) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA835 + difference 4 1) (sourceB835 + difference 1 4) sourceC835) = raw13773 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13773; decide +kernel
    rw [ha]
    exact (canonical13773 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA835 + difference 5 1) (sourceB835 + difference 1 5) sourceC835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2617) := by
    have ha : (tripleCharges (sourceA835 + difference 5 1) (sourceB835 + difference 1 5) sourceC835) = raw13774 := by
      apply Matrix.ext; unfold tripleCharges sourceA835 sourceB835 sourceC835 difference raw13774; decide +kernel
    rw [ha]
    exact (canonical13774 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA835 + sourceB835) sourceC835) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA835 + sourceB835) sourceC835) = raw13769 := by
      apply Matrix.ext; unfold doubleCharges sourceA835 sourceB835 sourceC835 raw13769; decide +kernel
    rw [ha]
    exact (canonical13769 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA835 sourceB835 sourceC835
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm835, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics
end OAI
