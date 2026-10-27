public section

noncomputable section

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

variable [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

variable [HasSheafify
  (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]

/-- Sheafification of the local-cohomology presheaf, functorial in the
coefficient sheaf. -/
@[expose] def sheafifiedLocalCohomologyFunctor (q : ℕ) :
    X.Sheaf AddCommGrpCat.{u} ⥤ Y.Sheaf AddCommGrpCat.{u} := by
  change CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
    CategoryTheory.Sheaf
      (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  exact localCohomologyPresheafFunctor f q ⋙
    presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}

end TopCat.Sheaf
end
end
