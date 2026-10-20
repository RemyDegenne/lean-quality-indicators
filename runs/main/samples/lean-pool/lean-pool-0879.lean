public section

open Set Filter

open scoped Topology BigOperators ContDiff InnerProductSpace

namespace NavierStokes.SolutionDifference

open ProblemStatement

theorem pressureGradient_contDiff {p : PressureField} {t : ℝ}
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x))) :
    ContDiff ℝ ∞ (pressureGradient p t) := by
  change ContDiff ℝ ∞ (fun x => ∑ i : Fin 3,
    fderiv ℝ (fun y => p (t, y)) x (coordinateVector i) • coordinateVector i)
  exact ContDiff.sum fun i _ => (spatial_partial_contDiff hp i).smul contDiff_const

end NavierStokes.SolutionDifference
end
