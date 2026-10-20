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

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective
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
lemma HPrimeIsoPushforwardResolutionHomologyPresheafObj_hom_open_naturality
    (q : ℕ) (hq : 0 < q) :
    (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) q).obj G).map
          ((Opens.map f).map i).op) ≫
        (HPrimeIsoPushforwardResolutionHomologyPresheafObj
          (G := G) f W q hq).hom =
      (HPrimeIsoPushforwardResolutionHomologyPresheafObj
          (G := G) f V q hq).hom ≫
        (pushforwardResolutionHomologyPresheaf f G q).map i.op := by
  dsimp [HPrimeIsoPushforwardResolutionHomologyPresheafObj]
  rw [← Category.assoc, ← Category.assoc,
    HPrimeIsoGlobalResolutionSectionsHomology_hom_open_naturality]
  simp only [Category.assoc]
  rw [globalResolutionSectionsIsoPushforwardResolutionSectionsHomology_hom_open_naturality_assoc]
  rw [pushforwardResolutionSectionsHomologyIso_hom_naturality]

end GlobalPushforwardIdentification
end AlongMap
end TopCat.Sheaf.RightDerivedPushforward
end
end
