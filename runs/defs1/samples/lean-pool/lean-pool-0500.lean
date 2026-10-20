@[expose] public section

noncomputable section

open Set Filter MeasureTheory

open scoped Topology ContDiff Interval BigOperators

namespace NavierStokes.NaturalCore

open ProblemStatement AxisymmetricFields

/-- Core potential, given by `potential (meridionalPotential h V) (swirlPotential h f)`. -/
noncomputable def corePotential (h : ℝ) (f V : ℝ × ℝ → ℝ) : VelocityField :=
  potential (meridionalPotential h V) (swirlPotential h f)

end NavierStokes.NaturalCore
end
end
