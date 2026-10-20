@[expose] public section

noncomputable section

namespace NavierStokes.ActualParticularCycleData

open Set Function Filter WeightedClasses CorrectionState CorrectionStep CorrectionInitialization

open scoped ContDiff Topology BigOperators

section NativeData

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}

theorem native_source_smooth (H : Invariant σ x) (l : Index B N0) (j : ℤ) (n : ℕ) :
    ContDiffOn ℝ ∞ ((nativeData x l j).source n)
      (ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
          ActualPrimary.standardRegion) := by
  rw [native_source_pull]
  apply (ActualCycleCoherence.source_smooth H ActualCoreSupport.refinedCarrier_closed
    (fun l n _ hz hc => ActualCycleCoherence.core_radius_pos l n hz hc) l j n).comp
  · exact (show ContDiff ℝ ∞ (fun z : ActualParticularStageControls.Native =>
      ActualCarrierTransport.associatedPoint z.1.1 z.2) by
        exact cycleAssoc.symm.contDiff.comp
          (contDiff_fst.fst.prodMk contDiff_snd)).contDiffOn
  · intro z hz
    exact hz.1

end NativeData
end NavierStokes.ActualParticularCycleData
end
end
