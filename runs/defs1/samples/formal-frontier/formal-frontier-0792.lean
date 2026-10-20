public section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology

universe u

variable {R : Type u} [CommRing R] [TopologicalSpace R]

variable {G : ProfiniteGrp.{u}}

/-- The topologized finite degree-zero diagrams, functorial in the coefficient
representation. -/
@[expose] noncomputable def topologicalFiniteZeroDeflationDiagramFunctor :
    Rep.{u} R G ⥤ (OpenNormalSubgroup G ⥤ TopModuleCat.{u} R) :=
  finiteZeroDeflationDiagramFunctor ⋙
    (Functor.whiskeringRight (OpenNormalSubgroup G) (ModuleCat R)
      (TopModuleCat.{u} R)).obj (TopModuleCat.withModuleTopology R)

end ContinuousGroupCohomology
end
