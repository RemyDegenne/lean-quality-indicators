@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite AlgebraicGeometry

universe u

namespace ContinuousFunctions

variable (X : Type u) [TopologicalSpace X]

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The commutative ring of germs of continuous `R`-valued functions at `x`. -/
abbrev stalk (x : X) : Type u := (sheaf X R).presheaf.stalk x

end ContinuousFunctions
end
end
