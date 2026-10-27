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

/-- The extension to `X` of the constant integral sheaf on the over-site at
`U`. -/
abbrev overConstantSource :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (restrictToOver U).leftAdjoint.obj
    ((constantSheaf ((Opens.grothendieckTopology X).over U)
      AddCommGrpCat.{u}).obj ↧(ULift ℤ))

end CategoryTheory.Sheaf.OpenCohomology
end
end
