@[expose] public section

noncomputable section

namespace NavierStokes.InitialPhysicalData

open Set Function Filter WeightedClasses HarmonicCalculus

open CorrectionInitialization ActualPrimaryBounds

open scoped Topology ContDiff BigOperators

attribute [local instance] Classical.propDecidable

section PhysicalFamilies

variable {B N0 : ℕ}

theorem copyPotential_field (B N0 : ℕ) : (copyPotential B N0).field = potential B N0 := rfl

end PhysicalFamilies
end NavierStokes.InitialPhysicalData
end
end
