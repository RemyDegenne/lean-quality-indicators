@[expose] public section

namespace NavierStokes.VariableGaugeMean

noncomputable section

open Set Function Filter MeasureTheory

open scoped ContDiff Topology Interval BigOperators

open WeightedRadialPrimitive RadialPullback

section TemporalLocal

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem temporalAtIndex_fiberLocal (h : ℝ) (n i : ℕ) :
    PhysicalMeanDomain.FiberLocal (S := S) (MeanChartCompatibility.temporalAtIndex h n i) := by
  intro f g s he r Y
  rw [MeanChartCompatibility.temporalAtIndex_eq_native,
      MeanChartCompatibility.temporalAtIndex_eq_native]
  exact congrArg (fun z : ℝ => MeanChartCompatibility.commonRatio h n i * z)
    (PhysicalMeanDomain.desiredIncrement_fiberLocal h n f g s he r Y)

end TemporalLocal
end
end NavierStokes.VariableGaugeMean
end
