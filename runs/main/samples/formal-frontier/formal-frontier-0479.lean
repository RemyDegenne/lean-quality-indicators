@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite AlgebraicGeometry

universe u

namespace ContinuousFunctions

variable (X : Type u) [TopologicalSpace X]

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

variable (K : Type u) [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T1Space K]

variable (Y : Type u) [TopologicalSpace Y]

theorem stalkMap_isLocalHom (f : X → Y) (hf : Continuous f) (x : X) :
    IsLocalHom ((locallyRingedSpaceMap X K Y f hf).stalkMap x).hom :=
  (locallyRingedSpaceMap X K Y f hf).prop x

end ContinuousFunctions
end
end
