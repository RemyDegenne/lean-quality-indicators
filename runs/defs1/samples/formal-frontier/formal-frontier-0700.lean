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

/-- Sheafifying the underlying pushed-forward resolution complex recovers the
pushed-forward sheaf complex. -/
@[expose] noncomputable def sheafifiedPushforwardResolutionComplexIso :
    ((presheafToSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (pushforwardResolutionPresheafComplex f G) ≅
      pushforwardResolutionSheafComplex f G :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((sheafificationNatIso
      (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).app
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj
          ((injectiveResolution G).cocomplex.X n))).symm)
    (by
      intro i j hij
      exact ((sheafificationNatIso
        (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).inv.naturality
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map
            ((injectiveResolution G).cocomplex.d i j))).symm)

end TopCat.Sheaf.RightDerivedPushforward
end
end
