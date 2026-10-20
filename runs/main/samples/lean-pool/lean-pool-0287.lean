@[expose] public section

noncomputable section

namespace NavierStokes.ActualSignedGeometry

open Set Function Filter WeightedClasses PhaseJetBounds PrimaryCopyBounds

open scoped ContDiff Topology BigOperators

section ActiveCopies

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {upper : ℝ} {B : ℕ} {r0 : ℝ} {N0 : ℕ}
  (a : PrimaryGeometryAssembly.Prepared H v upper B r0 N0)
  {vr vt : Plane}
  (sys : PartitionedCovariance.SlotSystem (CoordinateAlgebra.D F.data.h) F.data.h vr vt)
  (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
  (U : LocalSignedRequest.SlowRegion (2 * F.data.h))
  {Λ : Type} (reference : Λ → ℕ → Label H v a) (chart index : ℕ → ℕ)
  (sign : Λ → ℕ → Fin 2)

variable [Countable Λ] [Nonempty (ActivePair H v a reference chart)]

theorem active_reindexed_strip :
    viewStrip W U (activeChart H v a reference chart) =
      UniformPrimaryWeights.reindexedStrip (viewStrip W U chart)
        (fun q => ((activeEnumeration H v a reference chart q).val.2, ())) := rfl

end ActiveCopies
end NavierStokes.ActualSignedGeometry
end
end
