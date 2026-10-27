@[expose] public section

noncomputable section

open Set Filter Function

open scoped ContDiff Topology BigOperators

namespace NavierStokes.ConstructedSlowBase

open GlobalSlowProfiles AssembledSlowBase SlowBorelBase

/-- The genuine smooth vector potential of the summed base. -/
noncomputable def potential (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) :
    ProblemStatement.VelocityField :=
  AxisymmetricFields.potential (streamFactor a h C d) (swirlPotential a h C d)

end NavierStokes.ConstructedSlowBase
end
end
