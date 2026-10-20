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

section AlongMap

variable {Y : TopCat.{u}} (f : X ⟶ Y) (V : Opens Y)

variable [HasSheafify
  ((Opens.grothendieckTopology X).over ((Opens.map f).obj V))
    AddCommGrpCat.{u}]

variable [HasExt.{u} (CategoryTheory.Sheaf
  ((Opens.grothendieckTopology X).over ((Opens.map f).obj V))
    AddCommGrpCat.{u})]

variable [((Opens.grothendieckTopology X).over ((Opens.map f).obj V)).WEqualsLocallyBijective
  AddCommGrpCat.{u}]

variable [((Opens.grothendieckTopology X).over ((Opens.map f).obj V)).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]

section GlobalPushforwardIdentification

variable {W : Opens Y} (i : W ⟶ V)

omit [HasExt.{u} (CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget AddCommGrpCat.{u})]
  [HasSheafify
    ((Opens.grothendieckTopology X).over ((Opens.map f).obj V))
      AddCommGrpCat.{u}]
  [HasExt.{u} (CategoryTheory.Sheaf
    ((Opens.grothendieckTopology X).over ((Opens.map f).obj V))
      AddCommGrpCat.{u})]
  [((Opens.grothendieckTopology X).over
    ((Opens.map f).obj V)).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [((Opens.grothendieckTopology X).over
    ((Opens.map f).obj V)).HasSheafCompose
      (CategoryTheory.forget AddCommGrpCat.{u})] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma globalResolutionSectionsIsoPushforwardResolutionSections_hom_open_naturality :
    globalResolutionSectionsOpenMap ((Opens.map f).map i) G ≫
        (globalResolutionSectionsIsoPushforwardResolutionSections
          (G := G) f W).hom =
      (globalResolutionSectionsIsoPushforwardResolutionSections
          (G := G) f V).hom ≫
        pushforwardResolutionSectionsMap (G := G) (f := f)
          (V := V) (i := i) := by
  apply HomologicalComplex.hom_ext
  intro n
  dsimp [globalResolutionSectionsIsoPushforwardResolutionSections]
  simp only [Category.comp_id, Category.id_comp]
  exact HomologicalComplex.congr_hom
    (globalResolutionSectionsOpenMap_eq_pushforwardResolutionSectionsMap
      (G := G) f V i) n

end GlobalPushforwardIdentification
end AlongMap
end TopCat.Sheaf.RightDerivedPushforward
end
end
