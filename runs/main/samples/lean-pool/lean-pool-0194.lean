@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

namespace NavierStokes.PartitionedCovariance

open Set Function Filter MeasureTheory Matrix

open scoped BigOperators Topology ContDiff

theorem Pulse.profile_product (P : Pulse) (r : ℝ) (i : Fin 2) :
    (fun z => P.radialProfile r z * P.tangentProfile r i z) =
      TorusAverages.pulseProfile (cutoff r) P.ψ P.x P.t i := by
  funext z
  unfold Pulse.radialProfile Pulse.tangentProfile TorusAverages.pulseProfile
  ring

end NavierStokes.PartitionedCovariance
end
end
