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

/-- The canonical right-derived-functor comparison with the pushed-forward
fixed injective resolution. -/
@[expose] noncomputable def pushforwardIsoRightDerivedObj (q : ℕ) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived q).obj G ≅
      (pushforwardResolutionSheafComplex f G).homology q :=
  @InjectiveResolution.isoRightDerivedObj
    _ _ _ _ _ _ _ G (injectiveResolution G)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (pushforward_additive f) q

end TopCat.Sheaf.RightDerivedPushforward
end
end
