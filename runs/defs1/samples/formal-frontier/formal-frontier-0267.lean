public section

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf.RightDerivedPushforward

variable {X : TopCat.{u}} (U : Opens X)

variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

variable [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

open CategoryTheory.Sheaf.OpenCohomology

section GlobalCoefficientNaturality

variable {G H : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- The map on fixed-global-resolution section complexes induced by a
coefficient morphism. -/
@[expose] noncomputable def globalResolutionSectionsMap (a : G ⟶ H) :
    globalResolutionSections U G ⟶ globalResolutionSections U H :=
  ((openSectionsFunctor U).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (globalInjectiveResolutionHom a)

end GlobalCoefficientNaturality
end TopCat.Sheaf.RightDerivedPushforward
end
end
