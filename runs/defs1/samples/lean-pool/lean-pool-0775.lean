@[expose] public section

namespace NavierStokes.DefectIncrementBounds

noncomputable section

open Set Function MeasureTheory Filter

open scoped ContDiff Topology Interval

open WeightedClasses MeanIncrementBounds

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The radial chart has its actual radius and a coefficient smooth on the
physical positive radial region. No estimate on a residual is assumed. -/
structure PositiveOperators (o : Operators (Point P)) : Prop where
  radius_eq : o.radius = Prod.fst
  radialProfile : ContDiffOn ℝ ∞ o.radialProfile (positiveDomain (P := P))

end
end NavierStokes.DefectIncrementBounds
end
