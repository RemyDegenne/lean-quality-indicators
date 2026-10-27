@[expose] public section

noncomputable section

namespace NavierStokes.ActualPrimaryCoherence

open Set Function Filter HarmonicCalculus

open scoped Topology ContDiff InnerProductSpace

open CorrectionInitialization

open CorrectionInitialization.ActualPrimary

/-- Absolute angular, given by `(0,1)`. -/
noncomputable def absoluteAngular (_ : Absolute) : Absolute := (0,1)

end NavierStokes.ActualPrimaryCoherence
end
end
