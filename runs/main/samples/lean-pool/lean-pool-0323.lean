@[expose] public section

noncomputable section

namespace NavierStokes.CurrentSignedCurl

open Set Function Filter ProblemStatement HarmonicCalculus WeightedClasses

open CorrectionInitialization CorrectionInitialization.ActualPrimary

open ActualSignedCoherence ActualSignedPotentialCoherence

open scoped Topology ContDiff BigOperators

variable {B N0 : ℕ}

theorem currentPotential_sum_curl_map (s : Finset (SignedLabel B N0))
    (u : CorrectionState.State Point) {α : ℝ}
    (hamp : ∀ l ∈ s, AmplitudeBound l u α)
    (n : ℕ) {a : ℝ} (ha : 0 < a) (i : PolarCharts.Index) {qbig : ℝ} {z : SpaceTime}
    (hz : z ∈ ActualPhysicalPrefixFields.cartesianChartDomain qbig n a i) :
    SpatialCurl.spatialCurl (fun w => ∑ l ∈ s, currentPotential l u n a i w) z =
      CyclePhysicalPrefixes.polarVelocityMap a i
        (CyclePhysicalPrefixes.velocityMap (ActualCycleResidualBounds.actualBandGraph n)
          (∑ l ∈ s, ((ActualSignedStageControls.parameters l).exactBlock
            ActualInitialization.geometry.strip (request B u)).oscillation n)) z := by
  simpa only [map_sum, Finset.sum_apply] using
    currentPotential_sum_curl s u hamp n ha i hz

end NavierStokes.CurrentSignedCurl
end
end
