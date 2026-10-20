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

section Extend

variable {X} {m : ℕ} {Y : TopBranchedCover m}

variable (f : C(X.π ⁻¹' range toOnePoint, Y.π ⁻¹' range toOnePoint))
  (hπ : ∀ z, Y.π (f z) = X.π z)

theorem eq_extend {g : C(X.Z, Y.Z)} (hg : ∀ z : X.π ⁻¹' range toOnePoint, g z = f z) :
    g = extend f hπ :=
  ContinuousMap.ext <| congrFun (X.dense_preimage_range.extend_unique hg g.continuous).symm

end Extend
end TopBranchedCover
end TauCeti
end
end
