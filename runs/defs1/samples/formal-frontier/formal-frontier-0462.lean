public section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology

universe u

variable {R : Type u} [CommRing R] [TopologicalSpace R]

variable {G : ProfiniteGrp.{u}}

/-- The finite degree-`-1` deflation diagram, with every stage equipped with
its canonical module topology. -/
@[expose] noncomputable def topologicalFiniteNegativeOneDeflationDiagram
    (A : Rep.{u} R G) : OpenNormalSubgroup G ⥤ TopModuleCat.{u} R :=
  finiteNegativeOneDeflationDiagram A ⋙ TopModuleCat.withModuleTopology.{u, u} R

end ContinuousGroupCohomology
end
