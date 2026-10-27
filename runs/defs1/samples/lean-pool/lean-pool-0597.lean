section

@[expose] public section

noncomputable section

namespace NavierStokes.GlobalBaseError

open Set Filter ProblemStatement SlowBorelBase

open scoped Topology ContDiff

/-- Actual error, given by `FinalSlowBase.error FinalSlowBase.actualProfile.certificate
FinalSlowBase.actualProfile.modulation (actualUpper upper) B`. -/
noncomputable def actualError (upper : ℝ) (B : ℕ) : VelocityField :=
  FinalSlowBase.error FinalSlowBase.actualProfile.certificate FinalSlowBase.actualProfile.modulation
    (actualUpper upper) B

end NavierStokes.GlobalBaseError
end
end
end
