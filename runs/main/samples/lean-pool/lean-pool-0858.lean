section

@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped Topology ContDiff BigOperators

namespace NavierStokes.OutgoingPulseBounds

open OutgoingSchedule

theorem correction_log_eq_affineProfile (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) :
    correction c amp eta (Real.exp y) = affineProfile c (parameterPolynomial eta) (amp eta) y := by
  unfold correction LocalizedMomentRepair.repair affineProfile
  apply Finset.sum_congr rfl
  intro j _
  rw [bump_log_translate, debt_eq_affine]
  rfl

end NavierStokes.OutgoingPulseBounds
end
end
end
