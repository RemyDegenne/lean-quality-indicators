@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

/-- The `diamondOuterToThinKite` declaration. -/
noncomputable def diamondOuterToThinKite (δ : ℝ) (hδ : 0 < δ) :
    diamondPatch ≃ₜ thinKitePatch δ := by
  exact (thinKiteGlobalHomeomorph δ hδ).image diamondPatch

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
