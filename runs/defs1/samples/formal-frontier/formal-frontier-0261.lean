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

noncomputable local instance :
    (restrictToOver U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Adjunction.ofIsRightAdjoint (restrictToOver U))

noncomputable local instance : (restrictToOver U).Additive :=
  (restrictToOver U).additive_of_preserves_binary_products

variable (G : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- The restricted injective resolution, viewed as an acyclic resolution for
the constant integral source. -/
noncomputable abbrev restrictedAcyclicResolution :
    CategoryTheory.Abelian.Ext.AcyclicResolution
      ((constantSheaf ((Opens.grothendieckTopology X).over U)
        AddCommGrpCat.{u}).obj ↧(ULift ℤ))
      ((restrictToOver U).obj G) :=
  CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution _
    (restrictedInjectiveResolution U G)

end TopCat.Sheaf.RightDerivedPushforward
end
end
