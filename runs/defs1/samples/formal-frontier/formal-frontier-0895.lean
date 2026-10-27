public section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology

universe u

variable {R : Type u} [CommRing R] [TopologicalSpace R]

variable {G : ProfiniteGrp.{u}}

/-- The topological limit of the finite degree-`-1` deflation diagram. -/
noncomputable abbrev negativeOneDeflationLimit (A : Rep.{u} R G) :
    TopModuleCat.{u} R :=
  limit (topologicalFiniteNegativeOneDeflationDiagram A)

end ContinuousGroupCohomology
end
