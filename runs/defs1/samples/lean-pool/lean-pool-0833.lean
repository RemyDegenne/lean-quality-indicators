@[expose] public section

noncomputable section

open Set Filter MeasureTheory

open scoped Topology ContDiff

namespace NavierStokes.ExtendedHeatDebts

open HeatTailEdit OutgoingTail

open ParametricHeatTail (jetProduct jetProduct_nonneg jetProduct_continuousOn
  jetProduct_bound tailWeight tailDecay tailSize tailSize_nonneg tailWeight_continuousOn
  tailWeight_bound diffusion diffusion_contDiff diffusion_hasDerivAt)

/-- Normalized debt, given by `TerminalCompensation.scaledDebt K (physicalDebt d K η)`. -/
noncomputable def normalizedDebt (d : TailData) (K η : ℝ) : TerminalCompensation.Coeff :=
  TerminalCompensation.scaledDebt K (physicalDebt d K η)

end NavierStokes.ExtendedHeatDebts
end
end
