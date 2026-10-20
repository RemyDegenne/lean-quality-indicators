section

@[expose] public section

noncomputable section

namespace NavierStokes.ActualSignedFamilySupport

open Set Function Filter ProblemStatement CorrectionInitialization

open CorrectionInitialization.ActualPrimary PhysicalWaveSum PhysicalCopyBounds

open scoped Topology ContDiff

variable {B N0 : ℕ}
  (s : ∀ l : Label B N0, (ActualSignedPhysicalBinding.nativeViews l).StateData)

variable
  (hgeo : ∀ L : ActualSignedPhysicalData.NativeLabel (ActualSignedExterior.family s).active,
    ActualSignedPhysicalData.ReferenceGeometry slots ((ActualSignedExterior.family s).singleton L))

include hgeo

theorem pressure_support :
    LocalPhysicalCopyBounds.SupportData (pressureCopies s)
      ActualPolarCoverage.inner ActualPolarCoverage.outer h slots.radius 2 0 := by
  apply gated_assembled_support
  intro L
  exact PositiveTimeSignedData.pressure_support slots outgoing.data.h_pos.le
    ((ActualSignedExterior.family s).singleton L)
    (PositiveTimeSignedData.singletonLocalization s L) (hgeo L)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (PrimaryTargetBounds.leftRadius_pos nominal)
    (PrimaryTargetBounds.rightRadius_pos nominal)

end NavierStokes.ActualSignedFamilySupport
end
end
end
