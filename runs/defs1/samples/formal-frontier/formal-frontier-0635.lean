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

/-- The ringed space of continuous functions with values in a topological commutative ring. -/
@[implicit_reducible]
def ringedSpace : RingedSpace where
  carrier := TopCat.of X
  presheaf := (sheaf X R).presheaf
  IsSheaf := (sheaf X R).property

end ContinuousFunctions
end
end
