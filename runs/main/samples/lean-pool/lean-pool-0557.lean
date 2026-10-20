@[expose] public section

noncomputable section

namespace NavierStokes.CyclePhysicalPrefixes

open Set Filter Function ProblemStatement CorrectionState CorrectionStep

open MeanIncrementBounds

open scoped ContDiff Topology BigOperators

theorem pressure_polar_forward_germ {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index)
    (G : ScaledGraph) (n : ℕ) (p₀ : Cylinder → ℝ) (u : State CyclePoint)
    {z : SpaceTime} (hz : z ∈ PhysicalCurlCovariance.validCylindrical a j) :
    (fun w => pressure a j G n p₀ u (w.1, CylindricalResidual.chart w.2)) =ᶠ[𝓝 z]
      cylindricalPressure G n p₀ u :=
  eventually_of_mem ((PhysicalCurlCovariance.validCylindrical_open a j).mem_nhds hz)
    (fun _ hw => pressure_polar_forward ha j G n p₀ u hw)

end NavierStokes.CyclePhysicalPrefixes
end
end
