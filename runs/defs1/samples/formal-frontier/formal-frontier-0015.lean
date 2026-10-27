public section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology

universe u

variable {R : Type u} [CommRing R] [TopologicalSpace R]

variable {G : ProfiniteGrp.{u}}

/-- The topologized homological negative-deflation diagrams, functorial in the
coefficient representation. -/
@[expose] noncomputable def topologicalFiniteNegativeDeflationDiagramFunctor (n : ℕ) :
    Rep.{u} R G ⥤ (OpenNormalSubgroup G ⥤ TopModuleCat.{u} R) :=
  finiteNegativeDeflationDiagramFunctor n ⋙
    (Functor.whiskeringRight (OpenNormalSubgroup G) (ModuleCat R)
      (TopModuleCat.{u} R)).obj (TopModuleCat.withModuleTopology R)

end ContinuousGroupCohomology
end
