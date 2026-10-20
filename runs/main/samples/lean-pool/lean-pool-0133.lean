@[expose] public section

open Complex Set

open scoped ContDiff

theorem polytopeRoundedSupportCurve_regular
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (theta : ℝ) :
    deriv (polytopeRoundedSupportCurve u delta rho) theta ≠ 0 := by
  apply smoothSupportCurve_regular
    (contDiff_polytopeRoundedSupport hu delta rho)
  intro x
  unfold smoothSupportCurvatureRadius
  exact polytopeRoundedSupport_add_deriv_deriv_pos
    hu hdelta hrho x

end
