@[expose] public section

noncomputable section

open scoped MvPowerSeries.WithPiTopology

open PowerSeries Finset

namespace QSeries.FormalPowerSeries

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]

omit [TopologicalSpace R] [DiscreteTopology R] in
theorem one_sub_pow_mul_qPochhammerInv_succ (k : ℕ) :
    (1 - (X : R⟦X⟧) ^ (k + 1)) * qPochhammerInv (R := R) (k + 1) = qPochhammerInv k := by
  have h1 := qPochhammer_X_mul_qPochhammerInv (R := R) (k + 1)
  rw [qPochhammer_succ, ← pow_succ'] at h1
  refine (isUnit_qPochhammer_X (R := R) k).mul_left_cancel ?_
  rw [qPochhammer_X_mul_qPochhammerInv, ← mul_assoc, h1]

end QSeries.FormalPowerSeries
end
end
