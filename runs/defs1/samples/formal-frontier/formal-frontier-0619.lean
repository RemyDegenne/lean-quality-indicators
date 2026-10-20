public section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology

universe u

variable {R : Type u} [CommRing R] [TopologicalSpace R]

variable {G : ProfiniteGrp.{u}}

/-- The topological limit of the finite negative-deflation diagram in
homological degree `n`.  For positive `n`, this models Tate degree `-n-1`. -/
noncomputable abbrev negativeDeflationLimit (A : Rep.{u} R G) (n : ℕ) :
    TopModuleCat.{u} R :=
  limit (topologicalFiniteNegativeDeflationDiagram A n)

end ContinuousGroupCohomology
end
