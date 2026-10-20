@[expose] public section

namespace NavierStokes.VariableGaugeMean

noncomputable section

open Set Function Filter MeasureTheory

open scoped ContDiff Topology Interval BigOperators

section Gauge

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Compact alias, given by `RadialPullback.physicalAlias d (ell z.2.1 * a) (ell z.2.1 * b) M
((0 : S), v) f z`. -/
noncomputable def compactAlias (d a b M : ℝ) (ell : S → ℝ) (v : PressureStream.Plane)
    (f : PressureStream.Lift S → ℝ) (z : PressureStream.Lift S) : ℝ :=
  RadialPullback.physicalAlias d (ell z.2.1 * a) (ell z.2.1 * b) M ((0 : S), v) f z

end Gauge
end
end NavierStokes.VariableGaugeMean
end
