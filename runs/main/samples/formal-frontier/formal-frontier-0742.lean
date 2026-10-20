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

theorem locallyRingedSpaceMap_comp (Z : Type u) [TopologicalSpace Z]
    (f : X → Y) (hf : Continuous f) (g : Y → Z) (hg : Continuous g) :
    locallyRingedSpaceMap X K Z (g ∘ f) (hg.comp hf) =
      locallyRingedSpaceMap X K Y f hf ≫ locallyRingedSpaceMap Y K Z g hg := by
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.Hom.ext _ _ rfl ?_
  ext U representative
  rfl

end ContinuousFunctions
end
end
