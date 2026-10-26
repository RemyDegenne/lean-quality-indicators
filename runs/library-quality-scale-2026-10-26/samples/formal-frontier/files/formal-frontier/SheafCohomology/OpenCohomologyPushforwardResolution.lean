/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import SheafCohomology.InjectiveResolutionNaturality
public import SheafCohomology.LocalCohomology
public import SheafCohomology.OpenCohomology

public section

/-!
# Local cohomology and pushed-forward injective resolutions

This file compares positive-degree local cohomology over every target open with
the homology of the pushed-forward canonical injective resolution. It proves
naturality in open inclusions and coefficient sheaves and packages the
objectwise comparisons as an isomorphism of presheaves.

The construction uses a common small universe for spaces, coefficients, and Ext.
-/

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

/-- Pushforward of additive-commutative-group-valued sheaves is additive. -/
noncomputable instance pushforward_additive
    {Y : TopCat.{u}} (f : X ⟶ Y) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).additive_of_preserves_binary_products

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

/-- Sections over an open, valued in additive commutative groups. -/
abbrev openSectionsFunctor :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (CategoryTheory.sheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (.op U)

/-- The additive form of the free-Yoneda corepresentation of sections over
an open. -/
@[expose] noncomputable def cohomologySourceHomAddEquivSections
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) :
    (cohomologySource U ⟶ F) ≃+ ↑((openSectionsFunctor U).obj F) where
  toEquiv := (cohomologySourceCorepresentable U).homEquiv
  map_add' f g := by
    change ((f + g).hom.app (.op U)) _ =
      f.hom.app (.op U) _ + g.hom.app (.op U) _
    rfl

/-- Additive coyoneda from the free-Yoneda cohomology source is sections over
the corresponding open. -/
@[expose] noncomputable def cohomologySourceCoyonedaIsoSections :
    preadditiveCoyoneda.obj (.op (cohomologySource U)) ≅
      openSectionsFunctor U :=
  NatIso.ofComponents
    (fun F => (cohomologySourceHomAddEquivSections U F).toAddCommGrpIso)
    (by
      intro F G f
      ext x
      exact (cohomologySourceCorepresentable U).homEquiv_comp f x)

/-- The additive-coyoneda complex from the cohomology source into the fixed
canonical injective resolution. -/
noncomputable abbrev globalResolutionHomComplex
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) : CochainComplex AddCommGrpCat.{u} ℕ :=
  (CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution
    (cohomologySource U) (injectiveResolution G)).homComplex

/-- Sections over an open of the fixed canonical injective-resolution
complex. -/
noncomputable abbrev globalResolutionSections
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) : CochainComplex AddCommGrpCat.{u} ℕ :=
  ((openSectionsFunctor U).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (injectiveResolution G).cocomplex

/-- The additive-coyoneda resolution complex is the complex of sections over
the corresponding open. -/
@[expose] noncomputable def globalResolutionHomComplexIsoSections
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) :
    globalResolutionHomComplex U G ≅ globalResolutionSections U G :=
  (NatIso.mapHomologicalComplex (cohomologySourceCoyonedaIsoSections U)
    (ComplexShape.up ℕ)).app (injectiveResolution G).cocomplex

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

/-- Positive local cohomology as the homology of sections of the fixed
canonical injective resolution. -/
@[expose] noncomputable def HPrimeIsoGlobalResolutionSectionsHomology
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) (q : ℕ) (hq : 0 < q) :
    CategoryTheory.Sheaf.H' G q U ≅
      (globalResolutionSections U G).homology q :=
  HPrimeIsoGlobalResolutionHomComplexHomology U G q hq ≪≫
    HomologicalComplex.homologyMapIso
      (globalResolutionHomComplexIsoSections U G) q

/-- Positive local cohomology as the homology of sections of the fixed
canonical injective resolution, as an additive equivalence. -/
@[expose] noncomputable def HPrimeEquivGlobalResolutionSectionsHomology
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) (q : ℕ) (hq : 0 < q) :
    CategoryTheory.Sheaf.H' G q U ≃+
      ↑((globalResolutionSections U G).homology q) :=
  (HPrimeIsoGlobalResolutionSectionsHomology U G q hq
    ).addCommGroupIsoToAddEquiv

section GlobalOpenNaturality

variable {V W : Opens X} (i : W ⟶ V)

omit [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget AddCommGrpCat.{u})] in
set_option backward.isDefEq.respectTransparency false in
/-- The free-Yoneda additive-coyoneda/sections comparison is natural under
restriction of the open. -/
@[reassoc]
lemma cohomologySourceCoyonedaIsoSections_hom_open_naturality :
    preadditiveCoyoneda.map (globalCohomologySourceFunctor.map i).op ≫
        (cohomologySourceCoyonedaIsoSections W).hom =
      (cohomologySourceCoyonedaIsoSections V).hom ≫
        (CategoryTheory.sheafSections
          (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map i.op := by
  ext F x
  let x' : cohomologySource V ⟶ F := x
  let corepW := cohomologySourceCorepresentable W
  let corepV := cohomologySourceCorepresentable V
  have hsource :
      corepW.homEquiv (globalCohomologySourceFunctor.map i) =
        (sectionsRestrict i).app (cohomologySource V)
          (corepV.homEquiv (𝟙 _)) := by
    dsimp [corepW, corepV, cohomologySourceCorepresentable,
      globalCohomologySourceFunctor, sectionsRestrict]
    rw [← Category.comp_id
      ((presheafToSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).map
          (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free))]
    erw [(sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).homEquiv_naturality_left]
    erw [(AddCommGrpCat.adj.whiskerRight
      (Opens X)ᵒᵖ).homEquiv_naturality_left]
    exact (yonedaEquiv_naturality' _ i.op).symm
  change corepW.homEquiv (globalCohomologySourceFunctor.map i ≫ x') =
    (sectionsRestrict i).app F (corepV.homEquiv x')
  rw [corepW.homEquiv_comp, hsource]
  have hnat := ((sectionsRestrict i).naturality_apply x'
    (corepV.homEquiv (𝟙 _))).symm
  have hx :
      (sectionsAtType V).map x' (corepV.homEquiv (𝟙 _)) =
        corepV.homEquiv x' := by
    rw [← corepV.homEquiv_comp]
    simp
  calc
    _ = (sectionsRestrict i).app F
        ((sectionsAtType V).map x' (corepV.homEquiv (𝟙 _))) := hnat
    _ = _ := congrArg ((sectionsRestrict i).app F) hx

/-- Precomposition by the source map on the fixed resolution Hom complex. -/
@[expose] noncomputable def globalResolutionHomComplexOpenMap
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) :
    globalResolutionHomComplex V G ⟶ globalResolutionHomComplex W G :=
  (NatTrans.mapHomologicalComplex
    (preadditiveCoyoneda.map (globalCohomologySourceFunctor.map i).op)
      (ComplexShape.up ℕ)).app (injectiveResolution G).cocomplex

/-- Restriction of sections on the fixed injective-resolution complex. -/
@[expose] noncomputable def globalResolutionSectionsOpenMap
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) :
    globalResolutionSections V G ⟶ globalResolutionSections W G :=
  (NatTrans.mapHomologicalComplex
    ((CategoryTheory.sheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map i.op)
      (ComplexShape.up ℕ)).app (injectiveResolution G).cocomplex

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget AddCommGrpCat.{u})] in
/-- The positive Ext/fixed-resolution comparison is natural under restriction
of the open, viewed as precomposition by the free-Yoneda source map. -/
@[reassoc]
lemma HPrimeIsoGlobalResolutionHomComplexHomology_hom_open_naturality
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) (q : ℕ) (hq : 0 < q) :
    (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) q).obj G).map i.op) ≫
        (HPrimeIsoGlobalResolutionHomComplexHomology W G q hq).hom =
      (HPrimeIsoGlobalResolutionHomComplexHomology V G q hq).hom ≫
        HomologicalComplex.homologyMap
          (globalResolutionHomComplexOpenMap i G) q := by
  ext x
  exact CategoryTheory.Abelian.Ext.AcyclicResolution.injectiveExtPositiveIsoHomology_source_naturality
      (injectiveResolution G) (globalCohomologySourceFunctor.map i) q hq x

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget AddCommGrpCat.{u})] in
/-- The Hom-complex/sections comparison intertwines source precomposition and
restriction of sections. -/
@[reassoc]
lemma globalResolutionHomComplexIsoSections_hom_open_naturality
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) :
    globalResolutionHomComplexOpenMap i G ≫
        (globalResolutionHomComplexIsoSections W G).hom =
      (globalResolutionHomComplexIsoSections V G).hom ≫
        globalResolutionSectionsOpenMap i G := by
  apply HomologicalComplex.hom_ext
  intro n
  exact NatTrans.congr_app
    (cohomologySourceCoyonedaIsoSections_hom_open_naturality i)
    ((injectiveResolution G).cocomplex.X n)

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget AddCommGrpCat.{u})] in
/-- The Hom-complex/sections comparison intertwines the corresponding maps on
homology. -/
@[reassoc]
lemma globalResolutionHomComplexIsoSectionsHomology_hom_open_naturality
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) (q : ℕ) :
    HomologicalComplex.homologyMap
          (globalResolutionHomComplexOpenMap i G) q ≫
        (HomologicalComplex.homologyMapIso
          (globalResolutionHomComplexIsoSections W G) q).hom =
      (HomologicalComplex.homologyMapIso
          (globalResolutionHomComplexIsoSections V G) q).hom ≫
        HomologicalComplex.homologyMap
          (globalResolutionSectionsOpenMap i G) q := by
  dsimp [HomologicalComplex.homologyMapIso]
  rw [← HomologicalComplex.homologyMap_comp,
    globalResolutionHomComplexIsoSections_hom_open_naturality,
    HomologicalComplex.homologyMap_comp]

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget AddCommGrpCat.{u})] in
/-- The positive local-cohomology/fixed-resolution-sections comparison is
natural under restriction of the open. -/
@[reassoc]
lemma HPrimeIsoGlobalResolutionSectionsHomology_hom_open_naturality
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) (q : ℕ) (hq : 0 < q) :
    (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) q).obj G).map i.op) ≫
        (HPrimeIsoGlobalResolutionSectionsHomology W G q hq).hom =
      (HPrimeIsoGlobalResolutionSectionsHomology V G q hq).hom ≫
        HomologicalComplex.homologyMap
          (globalResolutionSectionsOpenMap i G) q := by
  dsimp [HPrimeIsoGlobalResolutionSectionsHomology]
  rw [← Category.assoc,
    HPrimeIsoGlobalResolutionHomComplexHomology_hom_open_naturality]
  simp only [Category.assoc]
  rw [globalResolutionHomComplexIsoSectionsHomology_hom_open_naturality]

end GlobalOpenNaturality

/-- Evaluation at the terminal object of the open over-site. -/
abbrev overTerminalSectionsFunctor :
    CategoryTheory.Sheaf
        ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u} :=
  (CategoryTheory.sheafSections
    ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}).obj
      (.op (Over.mk (𝟙 U)))

/-- Degree-zero cohomology on the open over-site is terminal evaluation. -/
@[expose] noncomputable def overFunctorHZeroIsoSections :
    CategoryTheory.Sheaf.functorH
        ((Opens.grothendieckTopology X).over U) 0 ≅
      overTerminalSectionsFunctor U :=
  NatIso.ofComponents
    (fun F => (CategoryTheory.Sheaf.H.equiv₀ F
      Over.mkIdTerminal).toAddCommGrpIso)
    (by
      intro F G f
      ext x
      exact (CategoryTheory.Sheaf.H.equiv₀_naturality
        Over.mkIdTerminal f x).symm)

/-- Additive coyoneda from the constant integral sheaf is terminal evaluation
on the open over-site. -/
@[expose] noncomputable def overCoyonedaIsoSections :
    preadditiveCoyoneda.obj
        (.op ((constantSheaf
          ((Opens.grothendieckTopology X).over U)
          AddCommGrpCat.{u}).obj ↧(ULift ℤ))) ≅
      overTerminalSectionsFunctor U :=
  (CategoryTheory.Abelian.Ext.extZeroCoyonedaIso
    ((constantSheaf ((Opens.grothendieckTopology X).over U)
      AddCommGrpCat.{u}).obj ↧(ULift ℤ))).symm ≪≫
    overFunctorHZeroIsoSections U

noncomputable local instance :
    (restrictToOver U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Adjunction.ofIsRightAdjoint (restrictToOver U))

noncomputable local instance : (restrictToOver U).Additive :=
  (restrictToOver U).additive_of_preserves_binary_products

variable (G : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- Restrict the canonical injective resolution to the open over-site. -/
noncomputable abbrev restrictedInjectiveResolution :
    InjectiveResolution ((restrictToOver U).obj G) :=
  (restrictToOver U).mapInjectiveResolution (injectiveResolution G)

/-- The restricted injective resolution, viewed as an acyclic resolution for
the constant integral source. -/
noncomputable abbrev restrictedAcyclicResolution :
    CategoryTheory.Abelian.Ext.AcyclicResolution
      ((constantSheaf ((Opens.grothendieckTopology X).over U)
        AddCommGrpCat.{u}).obj ↧(ULift ℤ))
      ((restrictToOver U).obj G) :=
  CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution _
    (restrictedInjectiveResolution U G)

/-- Terminal sections of the restricted injective-resolution complex. -/
noncomputable abbrev restrictedResolutionSections :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  ((overTerminalSectionsFunctor U).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (restrictedAcyclicResolution U G).cocomplex

/-- The additive-Hom complex in the acyclic-resolution comparison is the
terminal-sections complex. -/
@[expose] noncomputable def restrictedResolutionHomComplexIsoSections :
    (restrictedAcyclicResolution U G).homComplex ≅
      restrictedResolutionSections U G :=
  (NatIso.mapHomologicalComplex (overCoyonedaIsoSections U)
      (ComplexShape.up ℕ)).app (restrictedAcyclicResolution U G).cocomplex

/-- Positive local cohomology is the homology of terminal sections of the
restricted canonical injective resolution. -/
@[expose] noncomputable def HPrimeEquivRestrictedResolutionSectionsHomology
    (q : ℕ) (hq : 0 < q) :
    CategoryTheory.Sheaf.H' G q U ≃+
      ↑((restrictedResolutionSections U G).homology q) :=
  (HPrimeEquivHOver U G q).trans <|
    ((restrictedAcyclicResolution U G).extPositiveIsoHomology q hq).trans <|
      (HomologicalComplex.homologyMapIso
        (restrictedResolutionHomComplexIsoSections U G) q).addCommGroupIsoToAddEquiv

/-- The underlying presheaf complex of the pushed-forward canonical
injective-resolution complex. -/
noncomputable abbrev pushforwardResolutionPresheafComplex
    {Y : TopCat.{u}} (f : X ⟶ Y)
    (G : CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    CochainComplex (Y.Presheaf AddCommGrpCat.{u}) ℕ :=
  ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
      TopCat.Sheaf.forget AddCommGrpCat.{u} Y).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (injectiveResolution G).cocomplex

/-- Evaluation at an open of the underlying pushed-forward canonical
injective-resolution complex. -/
noncomputable abbrev pushforwardResolutionSections
    {Y : TopCat.{u}} (f : X ⟶ Y) (V : Opens Y)
    (G : CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (.op V)
      ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (pushforwardResolutionPresheafComplex f G)

/-- Pointwise homology of the underlying pushed-forward canonical
injective-resolution complex. -/
noncomputable abbrev pushforwardResolutionHomologyPresheaf
    {Y : TopCat.{u}} (f : X ⟶ Y)
    (G : CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) :
    Y.Presheaf AddCommGrpCat.{u} :=
  (pushforwardResolutionPresheafComplex f G).homology q

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

/-- Restriction to `f ⁻¹ V` followed by terminal evaluation agrees with
evaluation at `V` after pushforward. -/
@[expose] noncomputable def restrictedSectionsIsoPushforwardSections :
    restrictToOver ((Opens.map f).obj V) ⋙
        overTerminalSectionsFunctor ((Opens.map f).obj V) ≅
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
          TopCat.Sheaf.forget AddCommGrpCat.{u} Y) ⋙
        (evaluation _ _).obj (.op V) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The terminal-sections complex after restriction to `f ⁻¹ V` is
canonically isomorphic to evaluation at `V` of the pushed-forward complex. -/
@[expose] noncomputable def restrictedResolutionSectionsIsoPushforwardResolutionSections :
    restrictedResolutionSections ((Opens.map f).obj V) G ≅
      pushforwardResolutionSections f V G :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (restrictedSectionsIsoPushforwardSections f V).app
      ((injectiveResolution G).cocomplex.X n))
    (by
      intro i j hij
      exact ((restrictedSectionsIsoPushforwardSections f V).hom.naturality
        ((injectiveResolution G).cocomplex.d i j)).symm)

/-- Homology after evaluation agrees with evaluation of pointwise presheaf
homology. -/
@[expose] noncomputable def pushforwardResolutionSectionsHomologyIso (q : ℕ) :
    (pushforwardResolutionSections f V G).homology q ≅
      (pushforwardResolutionHomologyPresheaf f G q).obj (.op V) :=
  by
    letI : ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj
      (.op V)).PreservesZeroMorphisms := ⟨by intros; rfl⟩
    letI : ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj
        (.op V)).PreservesHomology :=
      ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj
        (.op V)).preservesHomology_of_preservesEpis_and_kernels
    exact ((pushforwardResolutionPresheafComplex f G).sc q).mapHomologyIso
      ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (.op V))

section OpenNaturality

variable {W : Opens Y} (i : W ⟶ V)

/-- Restriction on the evaluated pushed-forward injective-resolution
complex. -/
@[expose] noncomputable def pushforwardResolutionSectionsMap :
    pushforwardResolutionSections f V G ⟶
      pushforwardResolutionSections f W G := by
  letI := evaluation_preservesZero Y V
  letI := evaluation_preservesZero Y W
  exact (NatTrans.mapHomologicalComplex
      ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).map i.op)
        (ComplexShape.up ℕ)).app (pushforwardResolutionPresheafComplex f G)

set_option backward.isDefEq.respectTransparency false in
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
/-- Pointwise homology of the pushed-forward resolution is natural under
restriction of the ambient open. -/
@[reassoc]
lemma pushforwardResolutionSectionsHomologyIso_hom_naturality (q : ℕ) :
    HomologicalComplex.homologyMap
          (pushforwardResolutionSectionsMap (G := G) (f := f)
            (V := V) (i := i)) q ≫
        (pushforwardResolutionSectionsHomologyIso
          (G := G) f W q).hom =
        (pushforwardResolutionSectionsHomologyIso
          (G := G) f V q).hom ≫
        (pushforwardResolutionHomologyPresheaf f G q).map i.op := by
  let _ := evaluation_preservesZero Y V
  let _ := evaluation_preservesZero Y W
  let _ : ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj
      (.op V)).PreservesHomology :=
    ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj
      (.op V)).preservesHomology_of_preservesEpis_and_kernels
  let _ : ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj
      (.op W)).PreservesHomology :=
    ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj
      (.op W)).preservesHomology_of_preservesEpis_and_kernels
  change ShortComplex.homologyMap
      (((pushforwardResolutionPresheafComplex f G).sc q).mapNatTrans
        ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).map i.op)) ≫
        (((pushforwardResolutionPresheafComplex f G).sc q).mapHomologyIso
          ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (.op W))).hom =
    (((pushforwardResolutionPresheafComplex f G).sc q).mapHomologyIso
        ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (.op V))).hom ≫
      ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).map i.op).app
        ((pushforwardResolutionPresheafComplex f G).sc q).homology
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp

end OpenNaturality

/-- Positive local cohomology over `f ⁻¹ V` is the homology at `V` of the
pushed-forward canonical injective-resolution complex. -/
@[expose] noncomputable def localCohomologyEquivPushforwardResolutionSectionsHomology
    (q : ℕ) (hq : 0 < q) :
    CategoryTheory.Sheaf.H' G q ((Opens.map f).obj V) ≃+
      ↑((pushforwardResolutionSections f V G).homology q) :=
  (HPrimeEquivRestrictedResolutionSectionsHomology
    ((Opens.map f).obj V) G q hq).trans
      (HomologicalComplex.homologyMapIso
        (restrictedResolutionSectionsIsoPushforwardResolutionSections
          (G := G) f V) q).addCommGroupIsoToAddEquiv

/-- Positive local cohomology over `f ⁻¹ V` is the value at `V` of the
pointwise homology presheaf of the pushed-forward canonical injective
resolution. -/
@[expose] noncomputable def localCohomologyEquivPushforwardResolutionHomologyPresheafObj
    (q : ℕ) (hq : 0 < q) :
    CategoryTheory.Sheaf.H' G q ((Opens.map f).obj V) ≃+
      ↑((pushforwardResolutionHomologyPresheaf f G q).obj (.op V)) :=
  (localCohomologyEquivPushforwardResolutionSectionsHomology
    (G := G) f V q hq).trans
      (pushforwardResolutionSectionsHomologyIso
        (G := G) f V q).addCommGroupIsoToAddEquiv

section CoefficientNaturality

variable {H : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- The canonical descent of a coefficient morphism, restricted to the open
over-site. -/
@[expose] noncomputable def restrictedInjectiveResolutionHom (a : G ⟶ H) :
    (restrictedInjectiveResolution ((Opens.map f).obj V) G).cocomplex ⟶
      (restrictedInjectiveResolution ((Opens.map f).obj V) H).cocomplex :=
  ((restrictToOver ((Opens.map f).obj V)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
    (InjectiveResolution.desc a (injectiveResolution H)
      (injectiveResolution G))

/-- The restricted canonical descent as a morphism of acyclic resolutions. -/
@[expose] noncomputable def restrictedAcyclicResolutionHom (a : G ⟶ H) :
    CategoryTheory.Abelian.Ext.AcyclicResolution.Hom
      (restrictedAcyclicResolution ((Opens.map f).obj V) G)
      (restrictedAcyclicResolution ((Opens.map f).obj V) H)
      ((restrictToOver ((Opens.map f).obj V)).map a) where
  hom := restrictedInjectiveResolutionHom (G := G) f V a
  ι_f_zero_comp_hom_f_zero := by
    have h :
        (restrictedAcyclicResolution ((Opens.map f).obj V) G).ι ≫
            restrictedInjectiveResolutionHom (G := G) f V a =
          (CochainComplex.single₀ _).map
              ((restrictToOver ((Opens.map f).obj V)).map a) ≫
            (restrictedAcyclicResolution ((Opens.map f).obj V) H).ι := by
      dsimp [restrictedAcyclicResolution, restrictedInjectiveResolution,
        restrictedInjectiveResolutionHom, CategoryTheory.Functor.mapInjectiveResolution,
        CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution]
      erw [Category.assoc, ← Functor.map_comp]
      rw [InjectiveResolution.desc_commutes]
      rw [Functor.map_comp]
      erw [← Category.assoc]
      erw [← (HomologicalComplex.singleMapHomologicalComplex
        (restrictToOver ((Opens.map f).obj V)) (ComplexShape.up ℕ) 0).inv.naturality a]
      simp
    exact HomologicalComplex.congr_hom h 0

/-- The map on terminal-section complexes induced by a coefficient morphism. -/
@[expose] noncomputable def restrictedResolutionSectionsMap (a : G ⟶ H) :
    restrictedResolutionSections ((Opens.map f).obj V) G ⟶
      restrictedResolutionSections ((Opens.map f).obj V) H :=
  ((overTerminalSectionsFunctor ((Opens.map f).obj V)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
    (restrictedAcyclicResolutionHom (G := G) f V a).hom

omit [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [((Opens.grothendieckTopology X).over ((Opens.map f).obj V)).WEqualsLocallyBijective
    AddCommGrpCat.{u}] in
/-- The additive-Hom/terminal-sections complex comparison is natural in the
coefficient sheaf. -/
@[reassoc]
lemma restrictedResolutionHomComplexIsoSections_hom_naturality
    (a : G ⟶ H) :
    (restrictedAcyclicResolution ((Opens.map f).obj V) G).homComplexMap
          (restrictedAcyclicResolution ((Opens.map f).obj V) H)
          (restrictedAcyclicResolutionHom (G := G) f V a).hom ≫
        (restrictedResolutionHomComplexIsoSections
          ((Opens.map f).obj V) H).hom =
      (restrictedResolutionHomComplexIsoSections
          ((Opens.map f).obj V) G).hom ≫
        restrictedResolutionSectionsMap (G := G) f V a := by
  exact (NatIso.mapHomologicalComplex
    (overCoyonedaIsoSections ((Opens.map f).obj V))
    (ComplexShape.up ℕ)).hom.naturality
      (restrictedAcyclicResolutionHom (G := G) f V a).hom

omit [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [((Opens.grothendieckTopology X).over ((Opens.map f).obj V)).WEqualsLocallyBijective
    AddCommGrpCat.{u}] in
/-- Naturality on homology of the additive-Hom/terminal-sections comparison. -/
@[reassoc]
lemma restrictedResolutionHomComplexIsoSectionsHomology_hom_naturality
    (a : G ⟶ H) (q : ℕ) :
    HomologicalComplex.homologyMap
          ((restrictedAcyclicResolution ((Opens.map f).obj V) G).homComplexMap
            (restrictedAcyclicResolution ((Opens.map f).obj V) H)
            (restrictedAcyclicResolutionHom (G := G) f V a).hom) q ≫
        (HomologicalComplex.homologyMapIso
          (restrictedResolutionHomComplexIsoSections
            ((Opens.map f).obj V) H) q).hom =
      (HomologicalComplex.homologyMapIso
          (restrictedResolutionHomComplexIsoSections
            ((Opens.map f).obj V) G) q).hom ≫
        HomologicalComplex.homologyMap
          (restrictedResolutionSectionsMap (G := G) f V a) q := by
  dsimp [HomologicalComplex.homologyMapIso]
  rw [← HomologicalComplex.homologyMap_comp,
    restrictedResolutionHomComplexIsoSections_hom_naturality,
    HomologicalComplex.homologyMap_comp]

/-- The positive-degree acyclic-resolution comparison bundled in
`AddCommGrpCat`. -/
@[expose] noncomputable def restrictedAcyclicResolutionExtPositiveIso
    (q : ℕ) (hq : 0 < q) :
    (CategoryTheory.Sheaf.functorH
        ((Opens.grothendieckTopology X).over ((Opens.map f).obj V)) q).obj
          ((restrictToOver ((Opens.map f).obj V)).obj G) ≅
      (restrictedAcyclicResolution
        ((Opens.map f).obj V) G).homComplex.homology q where
  hom := AddCommGrpCat.ofHom
    ((restrictedAcyclicResolution ((Opens.map f).obj V) G
      ).extPositiveIsoHomology q hq).toAddMonoidHom
  inv := AddCommGrpCat.ofHom
    ((restrictedAcyclicResolution ((Opens.map f).obj V) G
      ).extPositiveIsoHomology q hq).symm.toAddMonoidHom
  hom_inv_id := by
    ext x
    exact ((restrictedAcyclicResolution ((Opens.map f).obj V) G
      ).extPositiveIsoHomology q hq).symm_apply_apply x
  inv_hom_id := by
    ext x
    exact ((restrictedAcyclicResolution ((Opens.map f).obj V) G
      ).extPositiveIsoHomology q hq).apply_symm_apply x

omit [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [((Opens.grothendieckTopology X).over ((Opens.map f).obj V)).WEqualsLocallyBijective
    AddCommGrpCat.{u}] in
/-- Naturality of the positive-degree acyclic-resolution comparison for the
restricted canonical descents. -/
@[reassoc]
lemma restrictedAcyclicResolution_extPositiveIsoHomology_hom_naturality
    (a : G ⟶ H) (q : ℕ) (hq : 0 < q) :
    (CategoryTheory.Sheaf.functorH
          ((Opens.grothendieckTopology X).over ((Opens.map f).obj V)) q).map
          ((restrictToOver ((Opens.map f).obj V)).map a) ≫
        (restrictedAcyclicResolutionExtPositiveIso
          (G := H) f V q hq).hom =
      (restrictedAcyclicResolutionExtPositiveIso
          (G := G) f V q hq).hom ≫
        HomologicalComplex.homologyMap
          ((restrictedAcyclicResolution ((Opens.map f).obj V) G).homComplexMap
            (restrictedAcyclicResolution ((Opens.map f).obj V) H)
            (restrictedAcyclicResolutionHom (G := G) f V a).hom) q := by
  ext x
  exact (restrictedAcyclicResolution ((Opens.map f).obj V) G
    ).extPositiveIsoHomology_naturality
      (restrictedAcyclicResolution ((Opens.map f).obj V) H)
      (restrictedAcyclicResolutionHom (G := G) f V a) q hq x

/-- The positive-degree local-cohomology comparison as an isomorphism in
`AddCommGrpCat`. -/
@[expose] noncomputable def HPrimeIsoRestrictedResolutionSectionsHomology
    (q : ℕ) (hq : 0 < q) :
    CategoryTheory.Sheaf.H' G q ((Opens.map f).obj V) ≅
      (restrictedResolutionSections ((Opens.map f).obj V) G).homology q :=
  (HPrimeIsoHOver ((Opens.map f).obj V) q).app G ≪≫
    restrictedAcyclicResolutionExtPositiveIso
      (G := G) f V q hq ≪≫
    HomologicalComplex.homologyMapIso
      (restrictedResolutionHomComplexIsoSections
        ((Opens.map f).obj V) G) q

omit [((Opens.grothendieckTopology X).over ((Opens.map f).obj V)).WEqualsLocallyBijective
  AddCommGrpCat.{u}] in
/-- The positive-degree local-cohomology/terminal-sections comparison is
natural in the coefficient sheaf. -/
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

section GlobalPushforwardIdentification

variable {W : Opens Y} (i : W ⟶ V)

/-- Sections of the fixed global injective resolution over `f ⁻¹ V` are
definitionally the evaluation at `V` of its pushed-forward complex. -/
@[expose] noncomputable def globalResolutionSectionsIsoPushforwardResolutionSections :
    globalResolutionSections ((Opens.map f).obj V) G ≅
      pushforwardResolutionSections f V G :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => Iso.refl _)
    (by intros; rfl)

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
/-- Under the definitional global-sections/pushforward identification,
restriction over a mapped open is the evaluated pushforward restriction. -/
lemma globalResolutionSectionsOpenMap_eq_pushforwardResolutionSectionsMap :
    globalResolutionSectionsOpenMap ((Opens.map f).map i) G =
      pushforwardResolutionSectionsMap (G := G) (f := f)
        (V := V) (i := i) := by
  rfl

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
/-- The componentwise global-sections/pushforward identification is natural
under restriction of the ambient open. -/
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
/-- The definitional global-sections/pushforward identification intertwines
the corresponding maps on homology. -/
@[reassoc]
lemma globalResolutionSectionsIsoPushforwardResolutionSectionsHomology_hom_open_naturality
    (q : ℕ) :
    HomologicalComplex.homologyMap
          (globalResolutionSectionsOpenMap ((Opens.map f).map i) G) q ≫
        (HomologicalComplex.homologyMapIso
          (globalResolutionSectionsIsoPushforwardResolutionSections
            (G := G) f W) q).hom =
      (HomologicalComplex.homologyMapIso
          (globalResolutionSectionsIsoPushforwardResolutionSections
            (G := G) f V) q).hom ≫
        HomologicalComplex.homologyMap
          (pushforwardResolutionSectionsMap (G := G) (f := f)
            (V := V) (i := i)) q := by
  dsimp [HomologicalComplex.homologyMapIso]
  rw [← HomologicalComplex.homologyMap_comp,
    globalResolutionSectionsIsoPushforwardResolutionSections_hom_open_naturality,
    HomologicalComplex.homologyMap_comp]

/-- Positive local cohomology over `f ⁻¹ V` is the value at `V` of the
pointwise homology presheaf of the pushed-forward fixed global injective
resolution. -/
@[expose] noncomputable def HPrimeIsoPushforwardResolutionHomologyPresheafObj
    (q : ℕ) (hq : 0 < q) :
    CategoryTheory.Sheaf.H' G q ((Opens.map f).obj V) ≅
      (pushforwardResolutionHomologyPresheaf f G q).obj (.op V) :=
  HPrimeIsoGlobalResolutionSectionsHomology
      ((Opens.map f).obj V) G q hq ≪≫
    HomologicalComplex.homologyMapIso
      (globalResolutionSectionsIsoPushforwardResolutionSections
        (G := G) f V) q ≪≫
    pushforwardResolutionSectionsHomologyIso (G := G) f V q

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
/-- The positive local-cohomology/pushed-forward-resolution comparison is
natural under restriction of the ambient open. -/
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

section PresheafPackaging

variable {Y : TopCat.{u}} (f : X ⟶ Y)
variable (G : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- Positive local cohomology over inverse images, as a presheaf on the
target, is pointwise homology of the pushed-forward fixed canonical injective
resolution. -/
@[expose] noncomputable def HPrimePushforwardResolutionHomologyPresheafIso
    (q : ℕ) (hq : 0 < q) :
    (Opens.map f).op ⋙
        (CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) q).obj G ≅
      pushforwardResolutionHomologyPresheaf f G q :=
  NatIso.ofComponents
    (fun V => HPrimeIsoPushforwardResolutionHomologyPresheafObj
      (G := G) f V.unop q hq)
    (by
      intro V W i
      exact
        HPrimeIsoPushforwardResolutionHomologyPresheafObj_hom_open_naturality
          (G := G) f V.unop i.unop q hq)

end PresheafPackaging

end TopCat.Sheaf.RightDerivedPushforward

namespace TopCat.Sheaf.RightDerivedPushforward

variable {X : TopCat.{u}} (U : Opens X)
variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

open CategoryTheory.Sheaf.OpenCohomology

section GlobalCoefficientNaturality

variable {G H : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- The canonical descent between the fixed global injective resolutions of a
coefficient morphism. -/
@[expose] noncomputable def globalInjectiveResolutionHom (a : G ⟶ H) :
    (injectiveResolution G).cocomplex ⟶
      (injectiveResolution H).cocomplex :=
  InjectiveResolution.desc a (injectiveResolution H)
    (injectiveResolution G)

/-- The canonical global descent as a morphism of `Ext`-acyclic
resolutions. -/
@[expose] noncomputable def globalAcyclicResolutionHom (a : G ⟶ H) :
    CategoryTheory.Abelian.Ext.AcyclicResolution.Hom
      (CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution
        (cohomologySource U) (injectiveResolution G))
      (CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution
        (cohomologySource U) (injectiveResolution H)) a where
  hom := globalInjectiveResolutionHom a
  ι_f_zero_comp_hom_f_zero :=
    HomologicalComplex.congr_hom
      (InjectiveResolution.desc_commutes a (injectiveResolution H)
        (injectiveResolution G)) 0

/-- The map of additive-coyoneda complexes induced by canonical global
injective-resolution descent. -/
@[expose] noncomputable def globalResolutionHomComplexMap (a : G ⟶ H) :
    globalResolutionHomComplex U G ⟶
      globalResolutionHomComplex U H :=
  (CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution
      (cohomologySource U) (injectiveResolution G)).homComplexMap
    (CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution
      (cohomologySource U) (injectiveResolution H))
    (globalAcyclicResolutionHom U a).hom

/-- The map on fixed-global-resolution section complexes induced by a
coefficient morphism. -/
@[expose] noncomputable def globalResolutionSectionsMap (a : G ⟶ H) :
    globalResolutionSections U G ⟶ globalResolutionSections U H :=
  ((openSectionsFunctor U).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (globalInjectiveResolutionHom a)

/-- The additive-Hom/sections complex comparison is natural in the
coefficient sheaf. -/
@[reassoc]
lemma globalResolutionHomComplexIsoSections_hom_coefficient_naturality
    (a : G ⟶ H) :
    globalResolutionHomComplexMap U a ≫
        (globalResolutionHomComplexIsoSections U H).hom =
      (globalResolutionHomComplexIsoSections U G).hom ≫
        globalResolutionSectionsMap U a := by
  exact (NatIso.mapHomologicalComplex
    (cohomologySourceCoyonedaIsoSections U)
    (ComplexShape.up ℕ)).hom.naturality
      (globalInjectiveResolutionHom a)

/-- Naturality on homology of the additive-Hom/sections comparison. -/
@[reassoc]
lemma globalResolutionHomComplexIsoSectionsHomology_hom_coefficient_naturality
    (a : G ⟶ H) (q : ℕ) :
    HomologicalComplex.homologyMap
          (globalResolutionHomComplexMap U a) q ≫
        (HomologicalComplex.homologyMapIso
          (globalResolutionHomComplexIsoSections U H) q).hom =
      (HomologicalComplex.homologyMapIso
          (globalResolutionHomComplexIsoSections U G) q).hom ≫
        HomologicalComplex.homologyMap
          (globalResolutionSectionsMap U a) q := by
  dsimp [HomologicalComplex.homologyMapIso]
  rw [← HomologicalComplex.homologyMap_comp,
    globalResolutionHomComplexIsoSections_hom_coefficient_naturality,
    HomologicalComplex.homologyMap_comp]

/-- The positive Ext/fixed-global-resolution comparison is natural in the
coefficient sheaf. -/
@[reassoc]
lemma HPrimeIsoGlobalResolutionHomComplexHomology_hom_coefficient_naturality
    (a : G ⟶ H) (q : ℕ) (hq : 0 < q) :
    ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) q).map a).app (.op U) ≫
        (HPrimeIsoGlobalResolutionHomComplexHomology U H q hq).hom =
      (HPrimeIsoGlobalResolutionHomComplexHomology U G q hq).hom ≫
        HomologicalComplex.homologyMap
          (globalResolutionHomComplexMap U a) q := by
  ext x
  exact
    (CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution
      (cohomologySource U) (injectiveResolution G)
    ).extPositiveIsoHomology_naturality
      (CategoryTheory.Abelian.Ext.AcyclicResolution.ofInjectiveResolution
        (cohomologySource U) (injectiveResolution H))
      (globalAcyclicResolutionHom U a) q hq x

/-- The positive local-cohomology/fixed-global-resolution-sections comparison
is natural in the coefficient sheaf. -/
@[reassoc]
lemma HPrimeIsoGlobalResolutionSectionsHomology_hom_coefficient_naturality
    (a : G ⟶ H) (q : ℕ) (hq : 0 < q) :
    ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) q).map a).app (.op U) ≫
        (HPrimeIsoGlobalResolutionSectionsHomology U H q hq).hom =
      (HPrimeIsoGlobalResolutionSectionsHomology U G q hq).hom ≫
        HomologicalComplex.homologyMap
          (globalResolutionSectionsMap U a) q := by
  dsimp [HPrimeIsoGlobalResolutionSectionsHomology]
  rw [← Category.assoc,
    HPrimeIsoGlobalResolutionHomComplexHomology_hom_coefficient_naturality]
  simp only [Category.assoc]
  rw [globalResolutionHomComplexIsoSectionsHomology_hom_coefficient_naturality]

end GlobalCoefficientNaturality

end TopCat.Sheaf.RightDerivedPushforward

namespace TopCat.Sheaf.RightDerivedPushforward

local instance sheafForget_additive_suffix (Y : TopCat.{u}) :
    (TopCat.Sheaf.forget AddCommGrpCat.{u} Y).Additive where
  map_add := by intros; rfl

local instance evaluation_preservesZero_suffix (Y : TopCat.{u}) (V : Opens Y) :
    ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj
      (.op V)).PreservesZeroMorphisms where
  map_zero := by intros; rfl

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable {G H : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- Pushing forward the canonical descent between fixed injective resolutions. -/
@[expose] noncomputable def pushforwardResolutionPresheafComplexMap (a : G ⟶ H) :
    pushforwardResolutionPresheafComplex f G ⟶
      pushforwardResolutionPresheafComplex f H :=
  ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
      TopCat.Sheaf.forget AddCommGrpCat.{u} Y).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (globalInjectiveResolutionHom a)

/-- Evaluating the pushed-forward canonical descent at an open. -/
@[expose] noncomputable def pushforwardResolutionSectionsCoefficientMap
    (V : Opens Y) (a : G ⟶ H) :
    pushforwardResolutionSections f V G ⟶
      pushforwardResolutionSections f V H :=
  (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (.op V)
      ).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (pushforwardResolutionPresheafComplexMap f a)

/-- The coefficient map on pointwise homology of the pushed-forward fixed
injective resolution. -/
@[expose] noncomputable def pushforwardResolutionHomologyPresheafMap
    (a : G ⟶ H) (q : ℕ) :
    pushforwardResolutionHomologyPresheaf f G q ⟶
      pushforwardResolutionHomologyPresheaf f H q :=
  HomologicalComplex.homologyMap
    (pushforwardResolutionPresheafComplexMap f a) q

omit [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- Evaluation commutes naturally with the coefficient map on homology. -/
@[reassoc]
lemma pushforwardResolutionSectionsHomologyIso_hom_coefficient_naturality
    (V : Opens Y) (a : G ⟶ H) (q : ℕ) :
    HomologicalComplex.homologyMap
          (pushforwardResolutionSectionsCoefficientMap f V a) q ≫
        (pushforwardResolutionSectionsHomologyIso
          (G := H) f V q).hom =
      (pushforwardResolutionSectionsHomologyIso
          (G := G) f V q).hom ≫
        (pushforwardResolutionHomologyPresheafMap f a q).app (.op V) := by
  let _ := evaluation_preservesZero_suffix Y V
  let _ : ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj
      (.op V)).PreservesHomology :=
    ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj
      (.op V)).preservesHomology_of_preservesEpis_and_kernels
  change ShortComplex.homologyMap
      (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj
          (.op V)).mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor _ _ q).map
          (pushforwardResolutionPresheafComplexMap f a))) ≫
      (((pushforwardResolutionPresheafComplex f H).sc q).mapHomologyIso
        ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (.op V))).hom =
    (((pushforwardResolutionPresheafComplex f G).sc q).mapHomologyIso
      ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (.op V))).hom ≫
      ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (.op V)).map
        (ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor _ _ q).map
            (pushforwardResolutionPresheafComplexMap f a)))
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ q).map
      (pushforwardResolutionPresheafComplexMap f a))
    ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (.op V))

omit [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- The definitional global-sections/pushforward comparison is natural in the
coefficient sheaf. -/
@[reassoc]
lemma globalResolutionSectionsIsoPushforwardResolutionSections_hom_coefficient_naturality
    (V : Opens Y) (a : G ⟶ H) :
    globalResolutionSectionsMap ((Opens.map f).obj V) a ≫
        (globalResolutionSectionsIsoPushforwardResolutionSections
          (G := H) f V).hom =
      (globalResolutionSectionsIsoPushforwardResolutionSections
          (G := G) f V).hom ≫
        pushforwardResolutionSectionsCoefficientMap f V a := by
  apply HomologicalComplex.hom_ext
  intro n
  rfl

omit [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- The global-sections/pushforward comparison intertwines coefficient maps
on homology. -/
@[reassoc]
lemma globalResolutionSectionsIsoPushforwardResolutionSectionsHomology_hom_coefficient_naturality
    (V : Opens Y) (a : G ⟶ H) (q : ℕ) :
    HomologicalComplex.homologyMap
          (globalResolutionSectionsMap ((Opens.map f).obj V) a) q ≫
        (HomologicalComplex.homologyMapIso
          (globalResolutionSectionsIsoPushforwardResolutionSections
            (G := H) f V) q).hom =
      (HomologicalComplex.homologyMapIso
          (globalResolutionSectionsIsoPushforwardResolutionSections
            (G := G) f V) q).hom ≫
        HomologicalComplex.homologyMap
          (pushforwardResolutionSectionsCoefficientMap f V a) q := by
  dsimp [HomologicalComplex.homologyMapIso]
  rw [← HomologicalComplex.homologyMap_comp,
    globalResolutionSectionsIsoPushforwardResolutionSections_hom_coefficient_naturality,
    HomologicalComplex.homologyMap_comp]

/-- The positive local-cohomology/pushed-forward-resolution comparison is
natural in the coefficient sheaf at each target open. -/
@[reassoc]
lemma HPrimeIsoPushforwardResolutionHomologyPresheafObj_hom_coefficient_naturality
    (V : Opens Y) (a : G ⟶ H) (q : ℕ) (hq : 0 < q) :
    ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) q).map a).app
          (.op ((Opens.map f).obj V)) ≫
        (HPrimeIsoPushforwardResolutionHomologyPresheafObj
          (G := H) f V q hq).hom =
      (HPrimeIsoPushforwardResolutionHomologyPresheafObj
          (G := G) f V q hq).hom ≫
        (pushforwardResolutionHomologyPresheafMap f a q).app (.op V) := by
  dsimp [HPrimeIsoPushforwardResolutionHomologyPresheafObj]
  rw [← Category.assoc, ← Category.assoc,
    HPrimeIsoGlobalResolutionSectionsHomology_hom_coefficient_naturality]
  simp only [Category.assoc]
  rw [globalResolutionSectionsIsoPushforwardResolutionSectionsHomology_hom_coefficient_naturality_assoc]
  rw [pushforwardResolutionSectionsHomologyIso_hom_coefficient_naturality]

/-- The positive local-cohomology/pushed-forward-resolution presheaf
comparison is natural in the coefficient sheaf. -/
@[reassoc]
lemma HPrimePushforwardResolutionHomologyPresheafIso_hom_coefficient_naturality
    (a : G ⟶ H) (q : ℕ) (hq : 0 < q) :
    Functor.whiskerLeft (Opens.map f).op
          ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
            (Opens.grothendieckTopology X) q).map a) ≫
        (HPrimePushforwardResolutionHomologyPresheafIso f H q hq).hom =
      (HPrimePushforwardResolutionHomologyPresheafIso f G q hq).hom ≫
        pushforwardResolutionHomologyPresheafMap f a q := by
  apply NatTrans.ext
  funext V
  exact HPrimeIsoPushforwardResolutionHomologyPresheafObj_hom_coefficient_naturality
    (G := G) f V.unop a q hq

end TopCat.Sheaf.RightDerivedPushforward
