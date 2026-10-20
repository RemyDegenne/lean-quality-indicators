@[expose] public section

noncomputable section PortComputability

open Filter Set Topology TopologicalSpace

section

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MeasureTheory ProbabilityTheory

open scoped BoundedContinuousFunction NNReal ZeroAtInfty

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

/-- The part of a function on the one-point compactification which vanishes at infinity. -/
noncomputable def onePointRemainder (g : C₀(OnePoint X, ℝ)) : C₀(X, ℝ) where
  toFun x := g (x : OnePoint X) - g OnePoint.infty
  continuous_toFun :=
    (g.continuous.comp OnePoint.continuous_coe).sub continuous_const
  zero_at_infty' := by
    have hg := (OnePoint.continuous_iff (g : OnePoint X → ℝ)).mp g.continuous
    rw [← Filter.coclosedCompact_eq_cocompact]
    simpa only [Function.comp_apply, sub_self] using hg.1.sub_const (g OnePoint.infty)

end MarkovProcess.PositiveC0ContractiveResolvent
end
end PortComputability
end
