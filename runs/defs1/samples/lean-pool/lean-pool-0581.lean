section

@[expose] public section

noncomputable section

namespace NavierStokes.ActualSignedPhysicalZeros

open Set Function Filter ProblemStatement PhysicalWaveSum PhysicalCopyBounds

open CorrectionInitialization CorrectionInitialization.ActualPrimary

open ActualSignedExterior

open scoped Topology ContDiff BigOperators

/-- Frequency: an abbreviation for `TorusInverse.Frequency`. -/
abbrev Frequency := TorusInverse.Frequency

end NavierStokes.ActualSignedPhysicalZeros
end
end
end
