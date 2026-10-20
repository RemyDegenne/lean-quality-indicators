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

section CoefficientNaturality

variable {H : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

omit [((Opens.grothendieckTopology X).over ((Opens.map f).obj V)).WEqualsLocallyBijective
  AddCommGrpCat.{u}] in
@[reassoc]
lemma HPrimeIsoRestrictedResolutionSectionsHomology_hom_naturality
    (a : G ⟶ H) (q : ℕ) (hq : 0 < q) :
    ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) q).map a).app
          (.op ((Opens.map f).obj V)) ≫
        (HPrimeIsoRestrictedResolutionSectionsHomology
          (G := H) f V q hq).hom =
      (HPrimeIsoRestrictedResolutionSectionsHomology
          (G := G) f V q hq).hom ≫
        HomologicalComplex.homologyMap
          (restrictedResolutionSectionsMap (G := G) f V a) q := by
  have hprime :
      ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
            (Opens.grothendieckTopology X) q).map a).app
            (.op ((Opens.map f).obj V)) ≫
          (HPrimeIsoHOver ((Opens.map f).obj V) q).hom.app H =
        (HPrimeIsoHOver ((Opens.map f).obj V) q).hom.app G ≫
          (CategoryTheory.Sheaf.functorH
            ((Opens.grothendieckTopology X).over ((Opens.map f).obj V)) q).map
              ((restrictToOver ((Opens.map f).obj V)).map a) := by
    ext x
    exact (HPrimeEquivHOver_naturality
      ((Opens.map f).obj V) a q x).symm
  dsimp [HPrimeIsoRestrictedResolutionSectionsHomology]
  rw [← Category.assoc, hprime]
  simp only [Category.assoc]
  rw [restrictedAcyclicResolution_extPositiveIsoHomology_hom_naturality_assoc]
  rw [restrictedResolutionHomComplexIsoSectionsHomology_hom_naturality]

end CoefficientNaturality
end AlongMap
end TopCat.Sheaf.RightDerivedPushforward
end
end
