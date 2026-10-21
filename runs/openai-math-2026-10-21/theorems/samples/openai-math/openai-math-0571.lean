namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1477 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1477 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 0) (sourceB1477 + difference 0 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1755) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 0) (sourceB1477 + difference 0 4) sourceC1477) = raw22566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22566; decide +kernel
    rw [ha]
    exact (canonical22566 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 1) (sourceB1477 + difference 1 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 1) (sourceB1477 + difference 1 4) sourceC1477) = raw22421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22421; decide +kernel
    rw [ha]
    exact (canonical22421 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 2) (sourceB1477 + difference 2 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 2) (sourceB1477 + difference 2 4) sourceC1477) = raw22567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22567; decide +kernel
    rw [ha]
    exact (canonical22567 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 3) (sourceB1477 + difference 3 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 3) (sourceB1477 + difference 3 4) sourceC1477) = raw22568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22568; decide +kernel
    rw [ha]
    exact (canonical22568 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 4) (sourceB1477 + difference 4 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3311) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 4) (sourceB1477 + difference 4 4) sourceC1477) = raw22416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22416; decide +kernel
    rw [ha]
    exact (canonical22416 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1477 + difference 4 5) (sourceB1477 + difference 5 4) sourceC1477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3312) := by
    have ha : (tripleCharges (sourceA1477 + difference 4 5) (sourceB1477 + difference 5 4) sourceC1477) = raw22455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1477 sourceB1477 sourceC1477 difference raw22455; decide +kernel
    rw [ha]
    exact (canonical22455 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1477 + sourceB1477) sourceC1477) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1477 + sourceB1477) sourceC1477) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1477 sourceB1477 sourceC1477 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1477 sourceB1477 sourceC1477
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1477, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics
end OAI
