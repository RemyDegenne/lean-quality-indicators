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

/-- The canonical map from the local-cohomology presheaf to the underlying
presheaf of its sheafification. -/
@[expose] def toSheafifiedLocalCohomology (q : ℕ) :
    localCohomologyPresheafFunctor f q ⟶
      sheafifiedLocalCohomologyFunctor f q ⋙
        TopCat.Sheaf.forget AddCommGrpCat.{u} Y :=
  Functor.whiskerLeft (localCohomologyPresheafFunctor f q)
    (sheafificationAdjunction
      (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).unit

end TopCat.Sheaf
end
end
