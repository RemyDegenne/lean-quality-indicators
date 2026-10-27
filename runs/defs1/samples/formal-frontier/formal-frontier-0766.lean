public section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology

universe u

variable {R : Type u} [CommRing R] [TopologicalSpace R]

variable {G : ProfiniteGrp.{u}}

/-- The finite negative-deflation diagram, with every stage equipped with its
canonical module topology.  For positive `n`, its stages model Tate degree
`-n-1`. -/
@[expose] noncomputable def topologicalFiniteNegativeDeflationDiagram
    (A : Rep.{u} R G) (n : ℕ) : OpenNormalSubgroup G ⥤ TopModuleCat.{u} R :=
  finiteNegativeDeflationDiagram A n ⋙ TopModuleCat.withModuleTopology.{u, u} R

end ContinuousGroupCohomology
end
