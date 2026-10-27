public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace CategoryTheory.Sheaf.OpenCohomology

variable {X : TopCat.{u}} (U : Opens X)

variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

variable [HasSheafify
  ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]

variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective
  AddCommGrpCat.{u}]

variable [(Opens.grothendieckTopology X).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]

variable [((Opens.grothendieckTopology X).over U).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]

/-- The functor of sections of a sheaf on `X` over `U`, valued in types. -/
abbrev sectionsAtType :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u} ⥤ Type u :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{u}) ⋙
      (evaluation _ _).obj (.op U)

end CategoryTheory.Sheaf.OpenCohomology
end
end
