public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace CategoryTheory.Sheaf.OpenCohomology

variable {X : TopCat.{u}} {U V : Opens X} (i : V ⟶ U)

variable [globalSheafify : HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

variable [overUSheafify : HasSheafify
  ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]

variable [overVSheafify : HasSheafify
  ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]

variable [overULocallyBijective :
  ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective
  AddCommGrpCat.{u}]

variable [overUSheafCompose :
  ((Opens.grothendieckTopology X).over U).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]

variable [overVLocallyBijective :
  ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
  AddCommGrpCat.{u}]

variable [overVSheafCompose :
  ((Opens.grothendieckTopology X).over V).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]

variable [overUExt : HasExt.{u} (CategoryTheory.Sheaf
  ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u})]

variable [overVExt : HasExt.{u} (CategoryTheory.Sheaf
  ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u})]

variable [globalExt : HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

section OpenComparison

/-- The sheafified free-Yoneda cohomology source, functorial in the open. -/
abbrev globalCohomologySourceFunctor :
    Opens X ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u} :=
  yoneda ⋙
    (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}

end OpenComparison
end CategoryTheory.Sheaf.OpenCohomology
end
end
