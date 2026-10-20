public section

noncomputable section

open Filter Set Topology OnePoint

namespace TauCeti

open ThricePuncturedSphere

universe u

namespace TopBranchedCover

attribute [instance] instTopologicalSpace instCompactSpace instConnectedSpace instT2Space
  instSecondCountableTopology

variable {n : ℕ} (X : TopBranchedCover n)

namespace Iso

variable {X} {Y W : TopBranchedCover n}

/-- The homeomorphism of the restricted total spaces induced by an isomorphism of topological
branched covers. -/
def restrict (ι : Iso X Y) : X.π ⁻¹' range toOnePoint ≃ₜ Y.π ⁻¹' range toOnePoint :=
  ι.toHomeomorph.subtype fun z ↦ by simp

end Iso
end TopBranchedCover
end TauCeti
end
end
