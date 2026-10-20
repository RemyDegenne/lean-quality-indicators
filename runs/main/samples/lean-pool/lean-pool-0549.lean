section

section

@[expose] public section

noncomputable section

namespace NavierStokes.ActualSignedUnmaskedBinding

open Set Function Filter CorrectionState CorrectionInitialization

open scoped ContDiff Topology

variable {B N0 : ℕ}

variable (P : SignedStressPrimitive.Patch) (u : State Point)
    (H : MeanStateRegularity.PrimitiveData ActualPrimary.standardRegion P.a P.b
      (ActualPrimary.commonContext B) u)
    (hp : GaugeMomentBalances.MovingField ActualPrimary.standardRegion P.a P.b u.pressure)

theorem localized_amplitude_eq {D I : Type} (a : PeriodizedWaveBounds.CopyData D I) (i : I) (n : ℕ)
    (x : D) :
    (a.localized i).amplitude n x = a.cutoff n i x • a.amplitude n i x := rfl

end NavierStokes.ActualSignedUnmaskedBinding
end
end
end
end
