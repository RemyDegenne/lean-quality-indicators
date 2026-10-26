/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import SheafCohomology.OpenCohomologyPushforwardResolution

public section

/-!
# Positive local cohomology as right-derived pushforward

For a continuous map between spaces in a common small universe, this file
identifies the sheafification of the positive-degree local-cohomology presheaf
with the corresponding right-derived pushforward. The comparison is natural in
the coefficient sheaf.

Degree zero and independently varying universes are outside this API.
-/

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

/-- Sheafification's canonical comparison between homology after mapping the
resolution complex and sheafification of its pointwise homology. -/
@[expose] noncomputable def sheafifiedPushforwardResolutionHomologyIso (q : ℕ) :
    (((presheafToSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (pushforwardResolutionPresheafComplex f G)).homology q ≅
      (presheafToSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).obj
          (pushforwardResolutionHomologyPresheaf f G q) := by
  letI : (presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive
      (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
  letI : (presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).PreservesHomology := inferInstance
  exact ((pushforwardResolutionPresheafComplex f G).sc q).mapHomologyIso
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})

/-- The sheafification of positive local cohomology is homology of the
pushed-forward fixed canonical injective resolution. -/
@[expose] noncomputable def sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
    (q : ℕ) (hq : 0 < q) :
    TopCat.Sheaf.sheafifiedLocalCohomology f G q ≅
      (pushforwardResolutionSheafComplex f G).homology q := by
  letI : (presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive
      (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
  letI : (presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).PreservesHomology := inferInstance
  exact
    (presheafToSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).mapIso
        (HPrimePushforwardResolutionHomologyPresheafIso f G q hq) ≪≫
      (sheafifiedPushforwardResolutionHomologyIso f G q).symm ≪≫
      HomologicalComplex.homologyMapIso
        (sheafifiedPushforwardResolutionComplexIso f G) q

/-- The canonical right-derived-functor comparison with the pushed-forward
fixed injective resolution. -/
@[expose] noncomputable def pushforwardIsoRightDerivedObj (q : ℕ) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived q).obj G ≅
      (pushforwardResolutionSheafComplex f G).homology q :=
  @InjectiveResolution.isoRightDerivedObj
    _ _ _ _ _ _ _ G (injectiveResolution G)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (pushforward_additive f) q

/-- Positive sheafified local cohomology agrees objectwise with the right
derived pushforward. -/
@[expose] noncomputable def sheafifiedLocalCohomologyIsoRightDerivedObj
    (q : ℕ) (hq : 0 < q) :
    TopCat.Sheaf.sheafifiedLocalCohomology f G q ≅
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived q).obj G := by
  exact
    sheafifiedLocalCohomologyIsoPushforwardResolutionHomology f G q hq ≪≫
      (pushforwardIsoRightDerivedObj f G q).symm

section CoefficientNaturality

variable {G₁ G₂ : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- Sheafification of the coefficient map on the pointwise homology
presheaf. -/
@[expose] noncomputable def sheafifiedPushforwardResolutionHomologyMap
    (a : G₁ ⟶ G₂) (q : ℕ) :
    (presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).obj
        (pushforwardResolutionHomologyPresheaf f G₁ q) ⟶
      (presheafToSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).obj
          (pushforwardResolutionHomologyPresheaf f G₂ q) :=
  (presheafToSheaf (Opens.grothendieckTopology Y)
    AddCommGrpCat.{u}).map
      (pushforwardResolutionHomologyPresheafMap f a q)

/-- Sheafification of the coefficient map on the pushed-forward presheaf
resolution complexes. -/
@[expose] noncomputable def sheafifiedPushforwardResolutionComplexMap
    (a : G₁ ⟶ G₂) :
    ((presheafToSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (pushforwardResolutionPresheafComplex f G₁) ⟶
      ((presheafToSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (pushforwardResolutionPresheafComplex f G₂) := by
  letI : (presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive
      (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
  exact ((presheafToSheaf (Opens.grothendieckTopology Y)
    AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (pushforwardResolutionPresheafComplexMap f a)

/-- The coefficient map on the pushed-forward fixed injective-resolution
complex in sheaves. -/
@[expose] noncomputable def pushforwardResolutionSheafComplexMap (a : G₁ ⟶ G₂) :
    pushforwardResolutionSheafComplex f G₁ ⟶
      pushforwardResolutionSheafComplex f G₂ :=
  ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (globalInjectiveResolutionHom a)

/-- Mapping the positive presheaf comparison through sheafification preserves
its coefficient-naturality square. -/
@[reassoc]
lemma sheafifiedHPrimePushforwardResolutionHomologyPresheafIso_hom_coefficient_naturality
    (a : G₁ ⟶ G₂) (q : ℕ) (hq : 0 < q) :
    ((TopCat.Sheaf.sheafifiedLocalCohomologyFunctor f q).map a) ≫
        ((presheafToSheaf (Opens.grothendieckTopology Y)
          AddCommGrpCat.{u}).mapIso
            (HPrimePushforwardResolutionHomologyPresheafIso
              f G₂ q hq)).hom =
      ((presheafToSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).mapIso
          (HPrimePushforwardResolutionHomologyPresheafIso
            f G₁ q hq)).hom ≫
        sheafifiedPushforwardResolutionHomologyMap f a q := by
  change (presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).map
        (Functor.whiskerLeft (Opens.map f).op
          ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
            (Opens.grothendieckTopology X) q).map a)) ≫
      (presheafToSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).map
          (HPrimePushforwardResolutionHomologyPresheafIso
            f G₂ q hq).hom =
    (presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).map
        (HPrimePushforwardResolutionHomologyPresheafIso
          f G₁ q hq).hom ≫
      (presheafToSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).map
          (pushforwardResolutionHomologyPresheafMap f a q)
  rw [← Functor.map_comp,
    HPrimePushforwardResolutionHomologyPresheafIso_hom_coefficient_naturality,
    Functor.map_comp]

omit [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- Sheafification's homology comparison is natural in the coefficient
descent. -/
@[reassoc]
lemma sheafifiedPushforwardResolutionMapHomologyIso_inv_coefficient_naturality
    (a : G₁ ⟶ G₂) (q : ℕ) :
    sheafifiedPushforwardResolutionHomologyMap f a q ≫
        (sheafifiedPushforwardResolutionHomologyIso f G₂ q).inv =
      (sheafifiedPushforwardResolutionHomologyIso f G₁ q).inv ≫
        HomologicalComplex.homologyMap
          (sheafifiedPushforwardResolutionComplexMap f a) q := by
  let _ := presheafToSheaf_preservesZero_sheafification (Y := Y)
  let _ := presheafToSheaf_preservesHomology_sheafification (Y := Y)
  change (presheafToSheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).map
        (ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor _ _ q).map
            (pushforwardResolutionPresheafComplexMap f a))) ≫
      (((pushforwardResolutionPresheafComplex f G₂).sc q).mapHomologyIso
        (presheafToSheaf (Opens.grothendieckTopology Y)
          AddCommGrpCat.{u})).inv =
    (((pushforwardResolutionPresheafComplex f G₁).sc q).mapHomologyIso
      (presheafToSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u})).inv ≫
      ShortComplex.homologyMap
        ((presheafToSheaf (Opens.grothendieckTopology Y)
          AddCommGrpCat.{u}).mapShortComplex.map
            ((HomologicalComplex.shortComplexFunctor _ _ q).map
              (pushforwardResolutionPresheafComplexMap f a)))
  exact ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ q).map
      (pushforwardResolutionPresheafComplexMap f a))
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})

omit [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- The complex comparison from sheafified underlying pushforward to sheaf
pushforward is natural in the coefficient descent. -/
@[reassoc]
lemma sheafifiedPushforwardResolutionComplexIso_hom_coefficient_naturality
    (a : G₁ ⟶ G₂) :
    sheafifiedPushforwardResolutionComplexMap f a ≫
        (sheafifiedPushforwardResolutionComplexIso f G₂).hom =
      (sheafifiedPushforwardResolutionComplexIso f G₁).hom ≫
        pushforwardResolutionSheafComplexMap f a := by
  apply HomologicalComplex.hom_ext
  intro n
  exact (sheafificationNatIso
    (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).inv.naturality
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map
        ((globalInjectiveResolutionHom a).f n))

omit [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- The sheafified-complex/pushed-forward-sheaf-complex comparison
intertwines coefficient maps on homology. -/
@[reassoc]
lemma sheafifiedPushforwardResolutionComplexHomologyIso_hom_coefficient_naturality
    (a : G₁ ⟶ G₂) (q : ℕ) :
    HomologicalComplex.homologyMap
          (sheafifiedPushforwardResolutionComplexMap f a) q ≫
        (HomologicalComplex.homologyMapIso
          (sheafifiedPushforwardResolutionComplexIso f G₂) q).hom =
      (HomologicalComplex.homologyMapIso
          (sheafifiedPushforwardResolutionComplexIso f G₁) q).hom ≫
        HomologicalComplex.homologyMap
          (pushforwardResolutionSheafComplexMap f a) q := by
  dsimp [HomologicalComplex.homologyMapIso]
  rw [← HomologicalComplex.homologyMap_comp,
    sheafifiedPushforwardResolutionComplexIso_hom_coefficient_naturality,
    HomologicalComplex.homologyMap_comp]

omit [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- The inverse right-derived-functor comparison is natural in the
coefficient sheaf for canonical injective-resolution descent. -/
@[reassoc]
lemma pushforwardIsoRightDerivedObj_inv_coefficient_naturality
    (a : G₁ ⟶ G₂) (q : ℕ) :
    HomologicalComplex.homologyMap
          (pushforwardResolutionSheafComplexMap f a) q ≫
        (pushforwardIsoRightDerivedObj f G₂ q).inv =
      (pushforwardIsoRightDerivedObj f G₁ q).inv ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived q).map a := by
  have h :
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived q).map a ≫
          (pushforwardIsoRightDerivedObj f G₂ q).hom =
        (pushforwardIsoRightDerivedObj f G₁ q).hom ≫
          HomologicalComplex.homologyMap
            (pushforwardResolutionSheafComplexMap f a) q := by
    exact @InjectiveResolution.isoRightDerivedObj_hom_naturality
      _ _ _ _ _ _ _ G₁ G₂ a (injectiveResolution G₁)
      (injectiveResolution G₂) (globalInjectiveResolutionHom a)
      (HomologicalComplex.congr_hom
        (InjectiveResolution.desc_commutes a
          (injectiveResolution G₂) (injectiveResolution G₁)) 0)
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
      (pushforward_additive f) q
  apply (pushforwardIsoRightDerivedObj f G₂ q).comp_inv_eq.mpr
  exact ((pushforwardIsoRightDerivedObj f G₁ q).eq_inv_comp.mpr h.symm).trans
    (Category.assoc _ _ _).symm

/-- The sheafified-local-cohomology/pushed-forward-resolution-homology
comparison is natural in the coefficient sheaf. -/
@[reassoc]
lemma sheafifiedLocalCohomologyIsoPushforwardResolutionHomology_hom_coefficient_naturality
    (a : G₁ ⟶ G₂) (q : ℕ) (hq : 0 < q) :
    ((TopCat.Sheaf.sheafifiedLocalCohomologyFunctor f q).map a) ≫
        (sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
          f G₂ q hq).hom =
      (sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
          f G₁ q hq).hom ≫
        HomologicalComplex.homologyMap
          (pushforwardResolutionSheafComplexMap f a) q := by
  have hcomp :
      ((((TopCat.Sheaf.sheafifiedLocalCohomologyFunctor f q).map a ≫
          ((presheafToSheaf (Opens.grothendieckTopology Y)
            AddCommGrpCat.{u}).mapIso
              (HPrimePushforwardResolutionHomologyPresheafIso
                f G₂ q hq)).hom) ≫
        (sheafifiedPushforwardResolutionHomologyIso f G₂ q).inv) ≫
        (HomologicalComplex.homologyMapIso
          (sheafifiedPushforwardResolutionComplexIso f G₂) q).hom) =
      ((((presheafToSheaf (Opens.grothendieckTopology Y)
            AddCommGrpCat.{u}).mapIso
              (HPrimePushforwardResolutionHomologyPresheafIso
                f G₁ q hq)).hom ≫
        (sheafifiedPushforwardResolutionHomologyIso f G₁ q).inv) ≫
        (HomologicalComplex.homologyMapIso
          (sheafifiedPushforwardResolutionComplexIso f G₁) q).hom) ≫
        HomologicalComplex.homologyMap
          (pushforwardResolutionSheafComplexMap f a) q := by
    have h₁ :=
      sheafifiedHPrimePushforwardResolutionHomologyPresheafIso_hom_coefficient_naturality
        f a q hq
    have h₂ :=
      sheafifiedPushforwardResolutionMapHomologyIso_inv_coefficient_naturality
        f a q
    have h₃ :=
      sheafifiedPushforwardResolutionComplexHomologyIso_hom_coefficient_naturality
        f a q
    have h₂' :
        ((((presheafToSheaf (Opens.grothendieckTopology Y)
                AddCommGrpCat.{u}).mapIso
                  (HPrimePushforwardResolutionHomologyPresheafIso
                    f G₁ q hq)).hom ≫
            sheafifiedPushforwardResolutionHomologyMap f a q) ≫
          (sheafifiedPushforwardResolutionHomologyIso f G₂ q).inv) =
        ((((presheafToSheaf (Opens.grothendieckTopology Y)
                AddCommGrpCat.{u}).mapIso
                  (HPrimePushforwardResolutionHomologyPresheafIso
                    f G₁ q hq)).hom ≫
            (sheafifiedPushforwardResolutionHomologyIso f G₁ q).inv) ≫
          HomologicalComplex.homologyMap
            (sheafifiedPushforwardResolutionComplexMap f a) q) := by
      exact (Category.assoc _ _ _).trans
        ((congrArg
          (fun k =>
            ((presheafToSheaf (Opens.grothendieckTopology Y)
                AddCommGrpCat.{u}).mapIso
                  (HPrimePushforwardResolutionHomologyPresheafIso
                    f G₁ q hq)).hom ≫ k) h₂).trans
          (Category.assoc _ _ _).symm)
    have h₃' :
        (((((presheafToSheaf (Opens.grothendieckTopology Y)
                  AddCommGrpCat.{u}).mapIso
                    (HPrimePushforwardResolutionHomologyPresheafIso
                      f G₁ q hq)).hom ≫
              (sheafifiedPushforwardResolutionHomologyIso f G₁ q).inv) ≫
            HomologicalComplex.homologyMap
              (sheafifiedPushforwardResolutionComplexMap f a) q) ≫
          (HomologicalComplex.homologyMapIso
            (sheafifiedPushforwardResolutionComplexIso f G₂) q).hom) =
        (((((presheafToSheaf (Opens.grothendieckTopology Y)
                  AddCommGrpCat.{u}).mapIso
                    (HPrimePushforwardResolutionHomologyPresheafIso
                      f G₁ q hq)).hom ≫
              (sheafifiedPushforwardResolutionHomologyIso f G₁ q).inv) ≫
            (HomologicalComplex.homologyMapIso
              (sheafifiedPushforwardResolutionComplexIso f G₁) q).hom) ≫
          HomologicalComplex.homologyMap
            (pushforwardResolutionSheafComplexMap f a) q) := by
      exact (Category.assoc _ _ _).trans
        ((congrArg
          (fun k =>
            (((presheafToSheaf (Opens.grothendieckTopology Y)
                AddCommGrpCat.{u}).mapIso
                  (HPrimePushforwardResolutionHomologyPresheafIso
                    f G₁ q hq)).hom ≫
              (sheafifiedPushforwardResolutionHomologyIso f G₁ q).inv) ≫ k) h₃).trans
          (Category.assoc _ _ _).symm)
    have h₁' := congrArg
      (fun k =>
        (k ≫ (sheafifiedPushforwardResolutionHomologyIso f G₂ q).inv) ≫
          (HomologicalComplex.homologyMapIso
            (sheafifiedPushforwardResolutionComplexIso f G₂) q).hom) h₁
    have h₂'' := congrArg
      (fun k => k ≫
        (HomologicalComplex.homologyMapIso
          (sheafifiedPushforwardResolutionComplexIso f G₂) q).hom) h₂'
    exact h₁'.trans (h₂''.trans h₃')
  have e₁ :
      (sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
          f G₁ q hq).hom =
        ((presheafToSheaf (Opens.grothendieckTopology Y)
            AddCommGrpCat.{u}).mapIso
              (HPrimePushforwardResolutionHomologyPresheafIso
                f G₁ q hq)).hom ≫
          (sheafifiedPushforwardResolutionHomologyIso f G₁ q).inv ≫
          (HomologicalComplex.homologyMapIso
            (sheafifiedPushforwardResolutionComplexIso f G₁) q).hom := rfl
  have e₂ :
      (sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
          f G₂ q hq).hom =
        ((presheafToSheaf (Opens.grothendieckTopology Y)
            AddCommGrpCat.{u}).mapIso
              (HPrimePushforwardResolutionHomologyPresheafIso
                f G₂ q hq)).hom ≫
          (sheafifiedPushforwardResolutionHomologyIso f G₂ q).inv ≫
          (HomologicalComplex.homologyMapIso
            (sheafifiedPushforwardResolutionComplexIso f G₂) q).hom := rfl
  refine (congrArg
    (fun k => (TopCat.Sheaf.sheafifiedLocalCohomologyFunctor f q).map a ≫ k)
      e₂).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine hcomp.trans ?_
  refine (congrArg
    (fun k => k ≫ HomologicalComplex.homologyMap
      (pushforwardResolutionSheafComplexMap f a) q)
      (Category.assoc _ _ _)).trans ?_
  exact congrArg
    (fun k => k ≫ HomologicalComplex.homologyMap
      (pushforwardResolutionSheafComplexMap f a) q) e₁.symm

/-- The positive sheafified-local-cohomology/right-derived-pushforward
comparison is natural in the coefficient sheaf. -/
@[reassoc]
lemma sheafifiedLocalCohomologyIsoRightDerivedObj_hom_coefficient_naturality
    (a : G₁ ⟶ G₂) (q : ℕ) (hq : 0 < q) :
    ((TopCat.Sheaf.sheafifiedLocalCohomologyFunctor f q).map a) ≫
        (sheafifiedLocalCohomologyIsoRightDerivedObj f G₂ q hq).hom =
      (sheafifiedLocalCohomologyIsoRightDerivedObj f G₁ q hq).hom ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived q).map a := by
  have hcomp :
      (((TopCat.Sheaf.sheafifiedLocalCohomologyFunctor f q).map a ≫
          (sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
            f G₂ q hq).hom) ≫
        (pushforwardIsoRightDerivedObj f G₂ q).inv) =
      (((sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
            f G₁ q hq).hom ≫
        (pushforwardIsoRightDerivedObj f G₁ q).inv) ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived q).map a) := by
    have h₁ :=
      sheafifiedLocalCohomologyIsoPushforwardResolutionHomology_hom_coefficient_naturality
        f a q hq
    have h₂ := pushforwardIsoRightDerivedObj_inv_coefficient_naturality f a q
    have h₂' :
        (((sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
              f G₁ q hq).hom ≫
            HomologicalComplex.homologyMap
              (pushforwardResolutionSheafComplexMap f a) q) ≫
          (pushforwardIsoRightDerivedObj f G₂ q).inv) =
        (((sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
              f G₁ q hq).hom ≫
            (pushforwardIsoRightDerivedObj f G₁ q).inv) ≫
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived q).map a) := by
      exact (Category.assoc _ _ _).trans
        ((congrArg
          (fun k =>
            (sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
              f G₁ q hq).hom ≫ k) h₂).trans
          (Category.assoc _ _ _).symm)
    have h₁' := congrArg
      (fun k => k ≫ (pushforwardIsoRightDerivedObj f G₂ q).inv) h₁
    exact h₁'.trans h₂'
  have e₁ :
      (sheafifiedLocalCohomologyIsoRightDerivedObj f G₁ q hq).hom =
        (sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
            f G₁ q hq).hom ≫
          (pushforwardIsoRightDerivedObj f G₁ q).inv := rfl
  have e₂ :
      (sheafifiedLocalCohomologyIsoRightDerivedObj f G₂ q hq).hom =
        (sheafifiedLocalCohomologyIsoPushforwardResolutionHomology
            f G₂ q hq).hom ≫
          (pushforwardIsoRightDerivedObj f G₂ q).inv := rfl
  refine (congrArg
    (fun k => (TopCat.Sheaf.sheafifiedLocalCohomologyFunctor f q).map a ≫ k)
      e₂).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine hcomp.trans ?_
  exact congrArg
    (fun k => k ≫
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived q).map a)
      e₁.symm

end CoefficientNaturality

/-- In positive degree, sheafified local cohomology along a continuous map is
the corresponding right-derived pushforward, naturally in the coefficient
sheaf. -/
@[expose] noncomputable def sheafifiedLocalCohomologyFunctorIsoRightDerived
    (q : ℕ) (hq : 0 < q) :
    TopCat.Sheaf.sheafifiedLocalCohomologyFunctor f q ≅
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived q :=
  NatIso.ofComponents
    (fun G => sheafifiedLocalCohomologyIsoRightDerivedObj f G q hq)
    (by
      intro G₁ G₂ a
      exact
        sheafifiedLocalCohomologyIsoRightDerivedObj_hom_coefficient_naturality
          f a q hq)

end TopCat.Sheaf.RightDerivedPushforward
