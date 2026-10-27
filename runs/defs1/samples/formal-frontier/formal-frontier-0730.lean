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

variable [HasSheafify
  ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]

variable [HasExt.{u} (CategoryTheory.Sheaf
  ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u})]

variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective
  AddCommGrpCat.{u}]

variable [(Opens.grothendieckTopology X).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]

variable [((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective
  AddCommGrpCat.{u}]

variable [((Opens.grothendieckTopology X).over U).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]

open CategoryTheory.Sheaf.OpenCohomology

local instance sheafForget_additive (Y : TopCat.{u}) :
    (TopCat.Sheaf.forget AddCommGrpCat.{u} Y).Additive where
  map_add := by intros; rfl

local instance evaluation_preservesZero (Y : TopCat.{u}) (V : Opens Y) :
    ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj
      (.op V)).PreservesZeroMorphisms where
  map_zero := by intros; rfl

local instance pushforwardSections_preservesZero
    {Y : TopCat.{u}} (f : X ⟶ Y) (V : Opens Y) :
    (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
        TopCat.Sheaf.forget AddCommGrpCat.{u} Y) ⋙
      (evaluation _ _).obj (.op V))).PreservesZeroMorphisms where
  map_zero := by intros; rfl

/-- Positive local cohomology as the homology of the additive-coyoneda complex
of the fixed canonical injective resolution. -/
@[expose] noncomputable def HPrimeIsoGlobalResolutionHomComplexHomology
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) (q : ℕ) (hq : 0 < q) :
    CategoryTheory.Sheaf.H' G q U ≅
      (globalResolutionHomComplex U G).homology q where
  hom := AddCommGrpCat.ofHom
    ((CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution
      (cohomologySource U) (injectiveResolution G)
    ).extPositiveIsoHomology q hq).toAddMonoidHom
  inv := AddCommGrpCat.ofHom
    ((CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution
      (cohomologySource U) (injectiveResolution G)
    ).extPositiveIsoHomology q hq).symm.toAddMonoidHom
  hom_inv_id := by
    ext x
    exact ((CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution
      (cohomologySource U) (injectiveResolution G)
    ).extPositiveIsoHomology q hq).symm_apply_apply x
  inv_hom_id := by
    ext x
    exact ((CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution
      (cohomologySource U) (injectiveResolution G)
    ).extPositiveIsoHomology q hq).apply_symm_apply x

end TopCat.Sheaf.RightDerivedPushforward
end
end
