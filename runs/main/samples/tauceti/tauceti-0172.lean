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

theorem isLocalPowerAt_localDegree (z : X.Z) : IsLocalPowerAt X.π z (X.localDegree z) :=
  (X.exists_isLocalPowerAt z).choose_spec

end TopBranchedCover
end TauCeti
end
end
