@[expose] public section

noncomputable section

namespace NavierStokes.ActualMeanPotentialRealization

open Set Filter Function ProblemStatement HarmonicCalculus

open scoped ContDiff Topology BigOperators

/-- The same local polar realization used by the physical cycle prefixes. -/
noncomputable def cartesianPotential (a : ℝ) (j : PolarCharts.Index)
    (G : ScaledGraph) (Ψ : Point → ℝ) : VelocityField :=
  CyclePhysicalPrefixes.polarVelocityMap a j (componentPotential G Ψ)

end NavierStokes.ActualMeanPotentialRealization
end
end
