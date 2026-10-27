@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

namespace NavierStokes.MeanRankUpdate

open Set Function MeasureTheory Filter

open scoped BigOperators ContDiff Topology

section PhysicalChart

/-- Normalized physical axial, constructed using `desiredAxialIncrement`. -/
noncomputable def normalizedPhysicalAxial (coord A B lam a b Q : ℝ)
    (d : ChartPoint → Debt) (p : ChartPoint) : ℝ :=
  desiredAxialIncrement lam
    (shapedAmplitude B (PhysicalCoordinateBounds.etaCoord coord
      (PhysicalCoordinateBounds.dilation coord Q (chartInput p)))) a b
    (Real.sqrt (PhysicalCoordinateBounds.qCoord coord (PhysicalCoordinateBounds.dilation coord Q
        (chartInput p))))
    ((PhysicalCoordinateBounds.qCoord coord (PhysicalCoordinateBounds.dilation coord Q (chartInput
        p))) ^ (-A))
    (scaleDebt (Real.sqrt Q) (Q ^ (-A)) (d p)) (Real.sqrt Q * p.1) / Q ^ (-A)

end PhysicalChart
end NavierStokes.MeanRankUpdate
end
end
