public section

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf.RightDerivedPushforward

local instance presheafToSheaf_preservesZero_sheafification
    {Y : TopCat.{u}}
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}] :
    (presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})

noncomputable local instance presheafToSheaf_preservesHomology_sheafification
    {Y : TopCat.{u}}
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}] :
    (presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).PreservesHomology := inferInstance

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

variable [HasSheafify
  (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]

variable [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

variable (G : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- The fixed canonical injective resolution after sheaf pushforward. -/
noncomputable abbrev pushforwardResolutionSheafComplex :
    CochainComplex (CategoryTheory.Sheaf
      (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) ℕ :=
  ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (injectiveResolution G).cocomplex

end TopCat.Sheaf.RightDerivedPushforward
end
end
