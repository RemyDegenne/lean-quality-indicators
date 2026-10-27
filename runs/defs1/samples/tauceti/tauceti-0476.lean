public noncomputable section

namespace TauCeti

open Function Metric Set Topology ThricePuncturedSphere PunctureFilling

namespace ConnectedCover

open FilledCover

variable {n : ℕ} (C : ConnectedCover (X := TopCat.of ThricePuncturedSphere) basePt n)

/-- The total space of `C` is homeomorphic to the total space of the cover obtained by deleting
the marked fibres from its filled branched cover, by the inclusion `E ↪ FilledCover`. -/
def connectedCoverHomeomorph :
    (C.cover : TopCat) ≃ₜ (C.toTopBranchedCover.connectedCover.cover : TopCat) :=
  (unpuncturedHomeomorph C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton).trans
    C.toTopBranchedCover.connectedCoverHomeomorph.symm

end ConnectedCover
end TauCeti
end
