/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Over

public section

/-!
# Cohomology of an open via its over-site

For an open `U` of a topological space `X`, this file identifies the value
`Sheaf.H' G n U` of the Ext-based cohomology presheaf with the cohomology
`Sheaf.H (G.over U) n` of the restriction of `G` to the over-site at `U`.

For an inclusion `i : V ⟶ U`, `HOverMap i G n` gives the intrinsic
restriction map between the two over-site cohomology groups. We prove its
identity and composition laws and show that `HPrimeEquivHOver` carries it to
the existing restriction map of `Sheaf.cohomologyPresheafFunctor`.

The construction uses the common space, coefficient, and Ext universe
supported by the current sheaf-cohomology API.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace CategoryTheory.Sheaf.OpenCohomology

variable {X : TopCat.{u}} (U : Opens X)
variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasSheafify
  ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective
  AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]
variable [((Opens.grothendieckTopology X).over U).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]

/-- Restriction of sheaves on `X` to the over-site at the open `U`. -/
abbrev restrictToOver :=
  (Opens.grothendieckTopology X).overPullback AddCommGrpCat.{u} U

/-- The functor of sections of a sheaf on `X` over `U`, valued in types. -/
abbrev sectionsAtType :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u} ⥤ Type u :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{u}) ⋙
      (evaluation _ _).obj (.op U)

/-- The sheafified free-Yoneda object representing sections over `U`. -/
abbrev cohomologySource :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)

/-- The free-Yoneda source corepresents sections of abelian sheaves over `U`. -/
@[expose] noncomputable def cohomologySourceCorepresentable :
    (sectionsAtType U).CorepresentableBy (cohomologySource U) where
  homEquiv {F} :=
    ((sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).homEquiv _ _).trans
        (((AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).homEquiv _ _).trans
          yonedaEquiv)
  homEquiv_comp g f := by
    dsimp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_naturality_right, yonedaEquiv_comp]
    rfl

/-- The extension to `X` of the constant integral sheaf on the over-site at
`U`. -/
abbrev overConstantSource :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (restrictToOver U).leftAdjoint.obj
    ((constantSheaf ((Opens.grothendieckTopology X).over U)
      AddCommGrpCat.{u}).obj ↧(ULift ℤ))

/-- Sections over the terminal object of the over-site after restricting from
`X`. -/
abbrev overSectionsAtType :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u} ⥤ Type u :=
  restrictToOver U ⋙
    (sheafSections ((Opens.grothendieckTopology X).over U)
      AddCommGrpCat.{u}).obj (.op (Over.mk (𝟙 U))) ⋙
        CategoryTheory.forget AddCommGrpCat.{u}

/-- The extended constant integral sheaf corepresents terminal-object sections
on the over-site. -/
@[expose] noncomputable def overConstantSourceCorepresentable :
    (overSectionsAtType U).CorepresentableBy (overConstantSource U) where
  homEquiv {F} :=
    ((Adjunction.ofIsRightAdjoint (restrictToOver U)).homEquiv _ _).trans
      (((constantSheafAdj ((Opens.grothendieckTopology X).over U)
        AddCommGrpCat.{u} Over.mkIdTerminal).homEquiv _ _).trans
          (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv)
  homEquiv_comp g f := by
    dsimp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_naturality_right]
    rfl

/-- Terminal-object sections on the over-site agree naturally with sections
over the corresponding open of `X`. -/
@[expose] noncomputable def overSectionsAtTypeIso :
    overSectionsAtType U ≅ sectionsAtType U :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The extended constant integral sheaf, viewed as a corepresenter of sections
over `U`. -/
@[expose] noncomputable def overConstantSourceCorepresentableForSections :
    (sectionsAtType U).CorepresentableBy (overConstantSource U) :=
  (overConstantSourceCorepresentable U).ofIso (overSectionsAtTypeIso U)

/-- The canonical isomorphism between the free-Yoneda cohomology source and
the left-adjoint image of the constant sheaf on the over-site at `U`. -/
@[expose] noncomputable def cohomologySourceIsoOverConstantSource :
    cohomologySource U ≅ overConstantSource U :=
  (cohomologySourceCorepresentable U).uniqueUpToIso
    (overConstantSourceCorepresentableForSections U)

/-- The canonical terminal object in the pointwise left-Kan-extension index
when the evaluated open lies below `U`. -/
@[expose] noncomputable def overLanIndexTerminalObj (V : (Opens X)ᵒᵖ)
    (hVU : V.unop ≤ U) :
    CostructuredArrow (Over.forget U).op V := by
  let o : Over U := Over.mk (Y := V.unop) (homOfLE hVU)
  exact CostructuredArrow.mk (Y := .op o) (eqToHom (by rfl))

/-- Terminality of `overLanIndexTerminalObj`. -/
@[expose] noncomputable def overLanIndexTerminal (V : (Opens X)ᵒᵖ)
    (hVU : V.unop ≤ U) :
    IsTerminal (overLanIndexTerminalObj U V hVU) := by
  let toTerminal (Z : CostructuredArrow (Over.forget U).op V) :
      Z ⟶ overLanIndexTerminalObj U V hVU :=
    CostructuredArrow.homMk
      (Over.homMk
        (U := Over.mk (Y := V.unop) (homOfLE hVU)) Z.hom.unop).op
  refine IsTerminal.ofUniqueHom toTerminal ?_
  intro Z m
  apply CostructuredArrow.hom_ext
  apply Quiver.Hom.unop_inj
  ext
  exact Subsingleton.elim _ _

omit
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).HasSheafCompose
    (CategoryTheory.forget AddCommGrpCat.{u})]
  [((Opens.grothendieckTopology X).over U).HasSheafCompose
    (CategoryTheory.forget AddCommGrpCat.{u})] in
/-- The pointwise left-Kan-extension index is empty outside `U`. -/
theorem overLanIndexIsEmpty (V : (Opens X)ᵒᵖ)
    (hVU : ¬ V.unop ≤ U) :
    IsEmpty (CostructuredArrow (Over.forget U).op V) :=
  ⟨fun Z => hVU ((leOfHom Z.hom.unop).trans (leOfHom Z.left.unop.hom))⟩

/-- Pointwise left Kan extension along the open over-site forgetful functor
preserves finite limits of abelian-group-valued presheaves. -/
noncomputable instance overForgetOpLan_preservesFiniteLimits :
    PreservesFiniteLimits
      ((Over.forget U).op.lan :
        ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
    ((Over.forget U).op.lan :
      ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) J
  intro V
  by_cases hVU : V.unop ≤ U
  · let : IsFiltered (CostructuredArrow (Over.forget U).op V) :=
      IsFiltered.of_isTerminal _ (overLanIndexTerminal U V hVU)
    let W := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
      (CostructuredArrow.proj (Over.forget U).op V)
    have _ : PreservesColimitsOfShape
        (CostructuredArrow (Over.forget U).op V)
        (CategoryTheory.forget AddCommGrpCat.{u}) := by infer_instance
    have _ : ReflectsLimitsOfShape J
        (CategoryTheory.forget AddCommGrpCat.{u}) := by infer_instance
    have _ : PreservesLimitsOfShape J
        (CategoryTheory.forget AddCommGrpCat.{u}) := by infer_instance
    let : PreservesLimitsOfShape J
        (colim :
          (CostructuredArrow (Over.forget U).op V ⥤ AddCommGrpCat.{u}) ⥤
            AddCommGrpCat.{u}) := by
      infer_instance
    let : PreservesLimitsOfShape J W := by infer_instance
    let : PreservesLimitsOfShape J (W ⋙ colim) :=
      comp_preservesLimitsOfShape W colim
    exact preservesLimitsOfShape_of_natIso
      (lanEvaluationIsoColim AddCommGrpCat.{u} (Over.forget U).op V).symm

  · let _ := overLanIndexIsEmpty U V hVU
    let W := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj
      (CostructuredArrow.proj (Over.forget U).op V)
    have hcolim : IsZero
        (colim :
          (CostructuredArrow (Over.forget U).op V ⥤ AddCommGrpCat.{u}) ⥤
            AddCommGrpCat.{u}) := by
      apply Functor.isZero
      intro F
      exact (isColimitEquivIsInitialOfIsEmpty AddCommGrpCat.{u} (colimit.cocone F)
        (colimit.isColimit F)).isZero
    have hzero : IsZero (W ⋙ colim) :=
      Functor.isZero _ (fun F => hcolim.obj (W.obj F))
    let : PreservesLimitsOfShape J (W ⋙ colim) :=
      (W ⋙ colim).preservesLimitsOfShape_of_isZero hzero J
    exact preservesLimitsOfShape_of_natIso
      (lanEvaluationIsoColim AddCommGrpCat.{u} (Over.forget U).op V).symm

/-- The left adjoint to restriction to an open over-site preserves finite
limits. -/
noncomputable instance restrictToOver_leftAdjoint_preservesFiniteLimits :
    PreservesFiniteLimits (restrictToOver U).leftAdjoint := by
  let G := Over.forget U
  let J := (Opens.grothendieckTopology X).over U
  let K := Opens.grothendieckTopology X
  have hconstruction : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback G
        AddCommGrpCat.{u} J K) := by
    have : PreservesFiniteLimits
        (G.op.lan ⋙ presheafToSheaf K AddCommGrpCat.{u}) :=
      comp_preservesFiniteLimits _ _
    apply comp_preservesFiniteLimits
  exact preservesFiniteLimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso G
      AddCommGrpCat.{u} J K).symm


omit
  [HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}] in
/-- Restriction to an open over-site preserves epimorphisms. -/
theorem restrictToOver_epi {F G : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (a : F ⟶ G) [Epi a] : Epi ((restrictToOver U).map a) := by
  have ha : CategoryTheory.Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology X) a.hom :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi'
      AddCommGrpCat.{u} a).2 inferInstance
  let hlocal : CategoryTheory.Sheaf.IsLocallySurjective
      ((restrictToOver U).map a) := by
    constructor
    intro V s
    rw [GrothendieckTopology.mem_over_iff]
    have himage : Sieve.overEquiv V
        (CategoryTheory.Presheaf.imageSieve
          ((restrictToOver U).map a).hom s) =
        CategoryTheory.Presheaf.imageSieve a.hom s := by
      ext W i
      dsimp [Sieve.overEquiv, Sieve.functorPushforward,
        Presieve.functorPushforward, CategoryTheory.Presheaf.imageSieve]
      constructor
      · rintro ⟨Z, g, h, ⟨t, ht⟩, rfl⟩
        refine ⟨F.obj.map h.op t, ?_⟩
        change a.hom.app (.op Z.left) t = G.obj.map g.left.op s at ht
        change a.hom.app (.op W) (F.obj.map h.op t) =
          G.obj.map (h ≫ g.left).op s
        calc
          _ = G.obj.map h.op (a.hom.app (.op Z.left) t) :=
            ConcreteCategory.congr_hom (a.hom.naturality h.op) t
          _ = G.obj.map h.op (G.obj.map g.left.op s) := by rw [ht]
          _ = G.obj.map (h ≫ g.left).op s := by
            rw [op_comp, G.obj.map_comp]
            rfl
      · rintro ⟨t, ht⟩
        refine ⟨Over.mk (i ≫ V.hom), Over.homMk i, 𝟙 W, ?_, by simp⟩
        exact ⟨t, ht⟩
    rw [himage]
    exact ha.imageSieve_mem s
  let := hlocal
  infer_instance

/-- Restriction to an open over-site preserves epimorphisms. -/
instance restrictToOver_preservesEpimorphisms :
    (restrictToOver U).PreservesEpimorphisms where
  preserves a _ := restrictToOver_epi U a

/-- Restriction to an open over-site preserves finite colimits. -/
noncomputable instance restrictToOver_preservesFiniteColimits :
    PreservesFiniteColimits (restrictToOver U) := by
  let : (restrictToOver U).Additive :=
    (restrictToOver U).additive_of_preserves_binary_products
  let : (restrictToOver U).PreservesHomology :=
    (restrictToOver U).preservesHomology_of_preservesEpis_and_kernels
  exact Functor.preservesFiniteColimits_of_preservesHomology _


section ExtComparison

variable [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable [HasExt.{u} (CategoryTheory.Sheaf
  ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u})]

/-- The Ext equivalence induced by the adjunction between extension from and
restriction to the over-site at `U`. -/
@[expose] noncomputable def overExtEquiv
    (F : CategoryTheory.Sheaf
      ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u})
    (G : CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Abelian.Ext ((restrictToOver U).leftAdjoint.obj F) G n ≃+
      Abelian.Ext F ((restrictToOver U).obj G) n := by
  let : (restrictToOver U).leftAdjoint.Additive :=
    (restrictToOver U).leftAdjoint.additive_of_preserves_binary_products
  let : (restrictToOver U).Additive :=
    (restrictToOver U).additive_of_preserves_binary_products
  exact Adjunction.extEquiv (Adjunction.ofIsRightAdjoint (restrictToOver U))

/-- Ext transport along `cohomologySourceIsoOverConstantSource`. -/
@[expose] noncomputable def cohomologySourceExtIso
    (G : CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Abelian.Ext (cohomologySource U) G n ≃+
      Abelian.Ext (overConstantSource U) G n :=
  (((Abelian.extFunctor n).mapIso
    (cohomologySourceIsoOverConstantSource U).symm.op).app G).addCommGroupIsoToAddEquiv

/-- The additive equivalence between Ext-based cohomology over `U` and the
cohomology of the restricted sheaf on the over-site at `U`. -/
@[expose] noncomputable def HPrimeEquivHOver
    (G : CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    CategoryTheory.Sheaf.H' G n U ≃+
      CategoryTheory.Sheaf.H ((restrictToOver U).obj G) n :=
  (cohomologySourceExtIso U G n).trans
    (overExtEquiv U
      ((constantSheaf ((Opens.grothendieckTopology X).over U)
        AddCommGrpCat.{u}).obj ↧(ULift ℤ)) G n)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of `HPrimeEquivHOver` in the coefficient sheaf. -/
theorem HPrimeEquivHOver_naturality
    {G G' : CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : G ⟶ G') (n : ℕ) (x : CategoryTheory.Sheaf.H' G n U) :
    CategoryTheory.Sheaf.H.map ((restrictToOver U).map f) n
        (HPrimeEquivHOver U G n x) =
      HPrimeEquivHOver U G' n
        (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) n).map f).app (.op U) x) := by
  let : (restrictToOver U).leftAdjoint.Additive :=
    (restrictToOver U).leftAdjoint.additive_of_preserves_binary_products
  let : (restrictToOver U).Additive :=
    (restrictToOver U).additive_of_preserves_binary_products
  simp [HPrimeEquivHOver, cohomologySourceExtIso, overExtEquiv,
    CategoryTheory.Sheaf.H.map_apply]
  rw [← (Adjunction.ofIsRightAdjoint
    (restrictToOver U)).extEquiv_naturality_right₀]
  congr 1
  exact ConcreteCategory.congr_hom
    ((((Abelian.extFunctor n).mapIso
      (cohomologySourceIsoOverConstantSource U).symm.op).hom.naturality f).symm) x

/-- `HPrimeEquivHOver` as a natural isomorphism in the coefficient sheaf. -/
@[expose] noncomputable def HPrimeIsoHOver (n : ℕ) :
    CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) n ⋙
        (evaluation _ _).obj (.op U) ≅
      restrictToOver U ⋙
        CategoryTheory.Sheaf.functorH
          ((Opens.grothendieckTopology X).over U) n :=
  NatIso.ofComponents
    (fun G => (HPrimeEquivHOver U G n).toAddCommGrpIso)
    (fun f => by
      ext x
      exact (HPrimeEquivHOver_naturality U f n x).symm)

end ExtComparison

end CategoryTheory.Sheaf.OpenCohomology

namespace CategoryTheory.Sheaf.OpenCohomology

variable {X : TopCat.{u}} {U V : Opens X} (i : V ⟶ U)
variable [globalSheafify : HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [overUSheafify : HasSheafify
  ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
variable [overVSheafify : HasSheafify
  ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
variable [overULocallyBijective :
  ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective
  AddCommGrpCat.{u}]
variable [overUSheafCompose :
  ((Opens.grothendieckTopology X).over U).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]
variable [overVLocallyBijective :
  ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
  AddCommGrpCat.{u}]
variable [overVSheafCompose :
  ((Opens.grothendieckTopology X).over V).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]

/-- Restriction between over-sites induced by an inclusion of opens. -/
abbrev inclusionRestrict :=
  (Opens.grothendieckTopology X).overMapPullback AddCommGrpCat.{u} i

omit
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
/-- Restriction along an inclusion of open over-sites preserves
epimorphisms. -/
theorem inclusionRestrict_epi
    {F G : CategoryTheory.Sheaf
      ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}}
    (a : F ⟶ G) [Epi a] : Epi ((inclusionRestrict i).map a) := by
  have ha : CategoryTheory.Sheaf.IsLocallySurjective a :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi'
      AddCommGrpCat.{u} a).2 inferInstance
  let : CategoryTheory.Sheaf.IsLocallySurjective
      ((inclusionRestrict i).map a) := by
    change CategoryTheory.Presheaf.IsLocallySurjective
      ((Opens.grothendieckTopology X).over V)
      (Functor.whiskerLeft (Over.map i).op a.hom)
    exact CategoryTheory.Presheaf.isLocallySurjective_whisker
      ((Opens.grothendieckTopology X).over V)
      ((Opens.grothendieckTopology X).over U) (Over.map i) a.hom
  exact (CategoryTheory.Sheaf.isLocallySurjective_iff_epi'
    AddCommGrpCat.{u} ((inclusionRestrict i).map a)).1 inferInstance

/-- Restriction along an inclusion of open over-sites preserves
epimorphisms. -/
noncomputable instance inclusionRestrict_preservesEpimorphisms :
    (inclusionRestrict i).PreservesEpimorphisms where
  preserves a _ := inclusionRestrict_epi i a

/-- Restriction along an inclusion of open over-sites preserves finite
colimits. -/
noncomputable instance inclusionRestrict_preservesFiniteColimits :
    PreservesFiniteColimits (inclusionRestrict i) := by
  let : (inclusionRestrict i).Additive :=
    (inclusionRestrict i).additive_of_preserves_binary_products
  let : (inclusionRestrict i).PreservesHomology :=
    (inclusionRestrict i).preservesHomology_of_preservesEpis_and_kernels
  exact Functor.preservesFiniteColimits_of_preservesHomology _
/-- Restriction along `V ⟶ U` carries the constant sheaf on `J.over U` to
the constant sheaf on `J.over V`. -/
@[expose] noncomputable def constantRestrictIso (M : AddCommGrpCat.{u}) :
    (constantSheaf ((Opens.grothendieckTopology X).over V)
        AddCommGrpCat.{u}).obj M ≅
      (inclusionRestrict i).obj
        ((constantSheaf ((Opens.grothendieckTopology X).over U)
          AddCommGrpCat.{u}).obj M) :=
  ((presheafToSheaf ((Opens.grothendieckTopology X).over V)
      AddCommGrpCat.{u}).mapIso
      ((Functor.constCompWhiskeringLeftIso (Over V)ᵒᵖ
        (C := AddCommGrpCat.{u}) (Over.map i).op).app M)).symm ≪≫
    ((Over.map i).pushforwardContinuousSheafificationCompatibility
      AddCommGrpCat.{u}
      ((Opens.grothendieckTopology X).over V)
      ((Opens.grothendieckTopology X).over U)).app
        ((Functor.const (Over U)ᵒᵖ).obj M)

/-- Restricting first to `U` and then along `V ⟶ U` agrees naturally with
restricting directly to `V`. -/
@[expose] noncomputable def restrictToOverCompIso :
    restrictToOver U ⋙ inclusionRestrict i ≅ restrictToOver V :=
  NatIso.ofComponents
    (fun F => CategoryTheory.Sheaf.pushforwardOverMapIso F i)
    (fun f => by
      ext W x
      rfl)

variable [overUExt : HasExt.{u} (CategoryTheory.Sheaf
  ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u})]
variable [overVExt : HasExt.{u} (CategoryTheory.Sheaf
  ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u})]
variable [globalExt : HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- The intrinsic cohomology restriction along an inclusion of ambient opens,
obtained by applying the exact over-site restriction functor and transporting
the constant source and restricted coefficient sheaf through their canonical
isomorphisms. -/
@[expose] noncomputable def HOverMap
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) (n : ℕ) :
    CategoryTheory.Sheaf.H (G.over U) n →+
      CategoryTheory.Sheaf.H (G.over V) n := by
  let : (inclusionRestrict i).Additive :=
    (inclusionRestrict i).additive_of_preserves_binary_products
  exact
    { toFun := fun x =>
        ((Abelian.Ext.mk₀
          (constantRestrictIso i ↧(ULift ℤ)).hom).comp
            (x.mapExactFunctor (inclusionRestrict i)) (zero_add n)).comp
              (Abelian.Ext.mk₀ ((restrictToOverCompIso i).app G).hom)
              (add_zero n)
      map_zero' := by simp
      map_add' := by simp }

set_option backward.isDefEq.respectTransparency false in
omit globalSheafify overUSheafify overVSheafify
  overULocallyBijective overUSheafCompose
  overVLocallyBijective overVSheafCompose
  overUExt overVExt globalExt in
/-- The sheafification unit commutes with the constant-sheaf transport along
an inclusion of opens. -/
theorem toSheafify_constantRestrictIso (M : AddCommGrpCat.{u}) :
    toSheafify ((Opens.grothendieckTopology X).over V)
        ((Functor.const (Over V)ᵒᵖ).obj M) ≫
      (constantRestrictIso (X := X) i M).hom.hom =
    (Functor.constCompWhiskeringLeftIso (Over V)ᵒᵖ
        (C := AddCommGrpCat.{u}) (Over.map i).op).inv.app M ≫
      (Over.map i).op.whiskerLeft
        (toSheafify ((Opens.grothendieckTopology X).over U)
          ((Functor.const (Over U)ᵒᵖ).obj M)) := by
  dsimp [constantRestrictIso]
  change _ ≫ (_ ≫ _) = _
  simp only [← Category.assoc]
  rw [← toSheafify_naturality]
  rw [Category.assoc,
    Functor.toSheafify_pullbackSheafificationCompatibility]

set_option backward.isDefEq.respectTransparency false in
omit globalSheafify overUSheafify
  overULocallyBijective overUSheafCompose
  overUExt globalExt in
/-- The constant-sheaf transport is compatible with the identity inclusion. -/
theorem constantRestrictIso_id (M : AddCommGrpCat.{u}) :
    (constantRestrictIso (X := X) (𝟙 U) M).hom =
      ((Opens.grothendieckTopology X).overMapPullbackId
        AddCommGrpCat.{u} U).inv.app
          ((constantSheaf ((Opens.grothendieckTopology X).over U)
            AddCommGrpCat.{u}).obj M) := by
  apply CategoryTheory.Sheaf.hom_ext
  dsimp [constantRestrictIso,
    GrothendieckTopology.overMapPullbackId,
    Functor.sheafPushforwardContinuousId']
  apply sheafify_hom_ext _ _ _
    ((inclusionRestrict (X := X) (𝟙 U)).obj
      ((constantSheaf ((Opens.grothendieckTopology X).over U)
        AddCommGrpCat.{u}).obj M)).property
  change _ ≫ (_ ≫ _) = _
  simp only [← Category.assoc]
  rw [← toSheafify_naturality]
  rw [Category.assoc,
    Functor.toSheafify_pullbackSheafificationCompatibility]
  ext W x
  exact ConcreteCategory.congr_hom
    ((toSheafify ((Opens.grothendieckTopology X).over U)
      ((Functor.const (Over U)ᵒᵖ).obj M)).naturality
        ((Over.mapId U).hom.app W.unop).op) x

set_option backward.isDefEq.respectTransparency false in
omit globalSheafify overUSheafify
  overULocallyBijective overUSheafCompose
  overUExt globalExt in
/-- The ambient restriction comparison is compatible with the identity
inclusion. -/
theorem restrictToOverCompIso_id
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) :
    ((restrictToOverCompIso (X := X) (𝟙 U)).app G).hom =
      ((Opens.grothendieckTopology X).overMapPullbackId
        AddCommGrpCat.{u} U).hom.app (G.over U) := by
  ext W x
  simp [restrictToOverCompIso,
    GrothendieckTopology.overMapPullbackId,
    Functor.sheafPushforwardContinuousId']
  rw [← G.obj.map_id]
  congr

set_option backward.isDefEq.respectTransparency false in
omit globalSheafify globalExt in
/-- The intrinsic over-site cohomology restriction is the identity for the
identity inclusion. -/
theorem HOverMap_id
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) (n : ℕ) :
    HOverMap (X := X) (𝟙 U) G n = AddMonoidHom.id _ := by
  let : (inclusionRestrict (X := X) (𝟙 U)).Additive :=
    (inclusionRestrict (X := X) (𝟙 U)).additive_of_preserves_binary_products
  ext x
  change
    ((Abelian.Ext.mk₀
      (constantRestrictIso (X := X) (𝟙 U) ↧(ULift ℤ)).hom).comp
        (x.mapExactFunctor (inclusionRestrict (X := X) (𝟙 U)))
        (zero_add n)).comp
      (Abelian.Ext.mk₀
        ((restrictToOverCompIso (X := X) (𝟙 U)).app G).hom)
      (add_zero n) = x
  rw [constantRestrictIso_id, restrictToOverCompIso_id]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [Abelian.Ext.mapExactFunctor_comp_mk₀_natTransApp]
  rw [Abelian.Ext.mk₀_comp_mk₀_assoc]
  simp

section Composition

variable {W : Opens X} (j : W ⟶ V)
variable [overWSheafify : HasSheafify
  ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u}]
variable [overWLocallyBijective :
  ((Opens.grothendieckTopology X).over W).WEqualsLocallyBijective
  AddCommGrpCat.{u}]
variable [overWSheafCompose :
  ((Opens.grothendieckTopology X).over W).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]
variable [overWExt : HasExt.{u} (CategoryTheory.Sheaf
  ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u})]

set_option backward.isDefEq.respectTransparency false in
omit globalSheafify overUSheafify overVSheafify
  overULocallyBijective overUSheafCompose
  overVLocallyBijective overVSheafCompose
  overUExt overVExt globalExt
  overWSheafify overWLocallyBijective overWSheafCompose overWExt in
/-- The ambient restriction comparison is compatible with composition of
open inclusions. -/
theorem restrictToOverCompIso_comp
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) :
    ((restrictToOverCompIso (X := X) (j ≫ i)).app G).hom =
      ((Opens.grothendieckTopology X).overMapPullbackComp
        AddCommGrpCat.{u} j i).inv.app (G.over U) ≫
        (inclusionRestrict (X := X) j).map
          ((restrictToOverCompIso (X := X) i).app G).hom ≫
        ((restrictToOverCompIso (X := X) j).app G).hom := by
  ext Z x
  simp [restrictToOverCompIso,
    GrothendieckTopology.overMapPullbackComp]
  change x = x
  rfl

set_option backward.isDefEq.respectTransparency false in
omit globalSheafify overUSheafify overVSheafify
  overULocallyBijective overUSheafCompose
  overVLocallyBijective overVSheafCompose
  overUExt overVExt globalExt
  overWSheafify overWLocallyBijective overWSheafCompose overWExt in
/-- The constant-sheaf transport is compatible with composition of open
inclusions. -/
theorem constantRestrictIso_comp (M : AddCommGrpCat.{u}) :
    (constantRestrictIso (X := X) (j ≫ i) M).hom =
      (constantRestrictIso (X := X) j M).hom ≫
        (inclusionRestrict (X := X) j).map
          (constantRestrictIso (X := X) i M).hom ≫
        ((Opens.grothendieckTopology X).overMapPullbackComp
          AddCommGrpCat.{u} j i).hom.app
            ((constantSheaf ((Opens.grothendieckTopology X).over U)
              AddCommGrpCat.{u}).obj M) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
    ((inclusionRestrict (X := X) (j ≫ i)).obj
      ((constantSheaf ((Opens.grothendieckTopology X).over U)
        AddCommGrpCat.{u}).obj M)).property
  rw [toSheafify_constantRestrictIso (i := j ≫ i)]
  change _ = _ ≫ (_ ≫ (_ ≫ _))
  simp only [← Category.assoc]
  rw [toSheafify_constantRestrictIso (i := j)]
  apply NatTrans.ext
  funext Z
  simp [GrothendieckTopology.overMapPullbackComp]
  have hinner := NatTrans.congr_app (toSheafify_constantRestrictIso
    (X := X) (i := i) M) (.op ((Over.map j).obj Z.unop))
  simp at hinner
  rw [← Category.assoc, hinner]
  exact (toSheafify ((Opens.grothendieckTopology X).over U)
    ((Functor.const (Over U)ᵒᵖ).obj M)).naturality
      ((Over.mapComp j i).hom.app Z.unop).op

set_option backward.isDefEq.respectTransparency false in
omit globalSheafify globalExt in
/-- Intrinsic over-site cohomology restrictions compose contravariantly. -/
theorem HOverMap_comp
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}) (n : ℕ) :
    HOverMap (X := X) (j ≫ i) G n =
      (HOverMap (X := X) j G n).comp (HOverMap (X := X) i G n) := by
  let : (inclusionRestrict (X := X) i).Additive :=
    (inclusionRestrict (X := X) i).additive_of_preserves_binary_products
  let : (inclusionRestrict (X := X) j).Additive :=
    (inclusionRestrict (X := X) j).additive_of_preserves_binary_products
  let : (inclusionRestrict (X := X) (j ≫ i)).Additive :=
    (inclusionRestrict (X := X) (j ≫ i)).additive_of_preserves_binary_products
  ext x
  dsimp [HOverMap]
  rw [constantRestrictIso_comp]
  have hamb := restrictToOverCompIso_comp (X := X) (i := i) (j := j) G
  change (restrictToOverCompIso (X := X) (j ≫ i)).hom.app G = _ at hamb
  rw [hamb]
  rw [Abelian.Ext.mapExactFunctor_comp]
  rw [Abelian.Ext.mapExactFunctor_comp]
  simp only [Abelian.Ext.mapExactFunctor_mk₀]
  conv_lhs =>
    rw [← Abelian.Ext.mk₀_comp_mk₀_assoc]
    rw [← Abelian.Ext.mk₀_comp_mk₀_assoc]
  have hnat := Abelian.Ext.mapExactFunctor_comp_mk₀_natTransApp x
    ((Opens.grothendieckTopology X).overMapPullbackComp
      AddCommGrpCat.{u} j i).hom
  rw [← hnat]
  conv_lhs =>
    rw [← Abelian.Ext.mk₀_comp_mk₀]
    rw [← Abelian.Ext.mk₀_comp_mk₀]
  rw [Abelian.Ext.comp_mapExactFunctor]
  simp only [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀_assoc]
  simp

end Composition

section OpenComparison

/-- The sheafified free-Yoneda cohomology source, functorial in the open. -/
abbrev globalCohomologySourceFunctor :
    Opens X ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u} :=
  yoneda ⋙
    (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}

/-- Restriction of sections from `U` to `V`. -/
abbrev sectionsRestrict :
    sectionsAtType U ⟶
      sectionsAtType V :=
  Functor.whiskerRight
    ((sheafSections (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).map i.op)
    (CategoryTheory.forget AddCommGrpCat.{u})

/-- The canonical comparison between direct extension from `V` and extension
first to `U` and then to `X`. -/
@[expose] noncomputable def overLeftAdjointCompIso :
    (restrictToOver V).leftAdjoint ≅
      (inclusionRestrict i).leftAdjoint ⋙
        (restrictToOver U).leftAdjoint :=
  (Adjunction.ofIsRightAdjoint (restrictToOver V)).leftAdjointUniq
    (((Adjunction.ofIsRightAdjoint (inclusionRestrict i)).comp
      (Adjunction.ofIsRightAdjoint (restrictToOver U))).ofNatIsoRight
        (restrictToOverCompIso i))

/-- The map between the two ambient cohomology source objects induced by an
inclusion `V ⟶ U`. -/
@[expose] noncomputable def overConstantSourceMap (M : AddCommGrpCat.{u}) :
    (restrictToOver V).leftAdjoint.obj
        ((constantSheaf ((Opens.grothendieckTopology X).over V)
          AddCommGrpCat.{u}).obj M) ⟶
      (restrictToOver U).leftAdjoint.obj
        ((constantSheaf ((Opens.grothendieckTopology X).over U)
          AddCommGrpCat.{u}).obj M) :=
  (overLeftAdjointCompIso i).hom.app
      ((constantSheaf ((Opens.grothendieckTopology X).over V)
        AddCommGrpCat.{u}).obj M) ≫
    (restrictToOver U).leftAdjoint.map
      (((Adjunction.ofIsRightAdjoint (inclusionRestrict i)).homEquiv _ _).symm
        (constantRestrictIso i M).hom)

set_option backward.isDefEq.respectTransparency false in
omit globalSheafify overUSheafify overVSheafify
  overULocallyBijective overUSheafCompose
  overVLocallyBijective overVSheafCompose
  overUExt overVExt globalExt in
/-- The adjunction mate of `overConstantSourceMap`. -/
theorem overConstantSourceMap_homEquiv (M : AddCommGrpCat.{u}) :
    ((Adjunction.ofIsRightAdjoint (restrictToOver V)).homEquiv _ _)
        (overConstantSourceMap i M) =
      (constantRestrictIso i M).hom ≫
        (inclusionRestrict i).map
          (((Adjunction.ofIsRightAdjoint (restrictToOver U)).homEquiv _ _)
            (𝟙 ((restrictToOver U).leftAdjoint.obj
              ((constantSheaf ((Opens.grothendieckTopology X).over U)
                AddCommGrpCat.{u}).obj M)))) ≫
        (restrictToOverCompIso i).hom.app
          ((restrictToOver U).leftAdjoint.obj
            ((constantSheaf ((Opens.grothendieckTopology X).over U)
              AddCommGrpCat.{u}).obj M)) := by
  have hleft :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app
      (Adjunction.ofIsRightAdjoint (restrictToOver V))
      (((Adjunction.ofIsRightAdjoint (inclusionRestrict i)).comp
        (Adjunction.ofIsRightAdjoint (restrictToOver U))).ofNatIsoRight
          (restrictToOverCompIso i))
      ((constantSheaf ((Opens.grothendieckTopology X).over V)
        AddCommGrpCat.{u}).obj M)
  have hleft' :
      ((Adjunction.ofIsRightAdjoint
          (restrictToOver V)).homEquiv _ _)
          ((overLeftAdjointCompIso i).hom.app
            ((constantSheaf ((Opens.grothendieckTopology X).over V)
              AddCommGrpCat.{u}).obj M)) =
        (((Adjunction.ofIsRightAdjoint (inclusionRestrict i)).comp
          (Adjunction.ofIsRightAdjoint (restrictToOver U))).ofNatIsoRight
            (restrictToOverCompIso i)).unit.app
              ((constantSheaf
                ((Opens.grothendieckTopology X).over V)
                AddCommGrpCat.{u}).obj M) := hleft
  have hleft'' :
      ((Adjunction.ofIsRightAdjoint
          (restrictToOver V)).homEquiv
        ((constantSheaf ((Opens.grothendieckTopology X).over V)
          AddCommGrpCat.{u}).obj M)
        ((restrictToOver U).leftAdjoint.obj
          ((inclusionRestrict i).leftAdjoint.obj
            ((constantSheaf ((Opens.grothendieckTopology X).over V)
              AddCommGrpCat.{u}).obj M))))
        ((overLeftAdjointCompIso i).hom.app
          ((constantSheaf ((Opens.grothendieckTopology X).over V)
            AddCommGrpCat.{u}).obj M)) =
      (((Adjunction.ofIsRightAdjoint (inclusionRestrict i)).comp
        (Adjunction.ofIsRightAdjoint (restrictToOver U))).ofNatIsoRight
          (restrictToOverCompIso i)).unit.app
            ((constantSheaf ((Opens.grothendieckTopology X).over V)
              AddCommGrpCat.{u}).obj M) := hleft'
  have hamb :
      ((Adjunction.ofIsRightAdjoint (restrictToOver U)).homEquiv _ _)
          ((restrictToOver U).leftAdjoint.map
            (((Adjunction.ofIsRightAdjoint
              (inclusionRestrict i)).homEquiv _ _).symm
                (constantRestrictIso i M).hom)) =
        (((Adjunction.ofIsRightAdjoint
            (inclusionRestrict i)).homEquiv _ _).symm
              (constantRestrictIso i M).hom) ≫
          ((Adjunction.ofIsRightAdjoint (restrictToOver U)).homEquiv _ _)
            (𝟙 _) := by
    rw [← Category.comp_id
      ((restrictToOver U).leftAdjoint.map
        (((Adjunction.ofIsRightAdjoint
          (inclusionRestrict i)).homEquiv _ _).symm
            (constantRestrictIso i M).hom))]
    exact (Adjunction.ofIsRightAdjoint
      (restrictToOver U)).homEquiv_naturality_left _ _
  have hincl :
      ((Adjunction.ofIsRightAdjoint (inclusionRestrict i)).homEquiv _ _)
          ((((Adjunction.ofIsRightAdjoint
              (inclusionRestrict i)).homEquiv _ _).symm
                (constantRestrictIso i M).hom) ≫
            ((Adjunction.ofIsRightAdjoint (restrictToOver U)).homEquiv _ _)
              (𝟙 _)) =
        (constantRestrictIso i M).hom ≫
          (inclusionRestrict i).map
            (((Adjunction.ofIsRightAdjoint
              (restrictToOver U)).homEquiv _ _) (𝟙 _)) := by
    rw [(Adjunction.ofIsRightAdjoint
      (inclusionRestrict i)).homEquiv_naturality_right]
    rw [Equiv.apply_symm_apply]
  have htrans :
      (((Adjunction.ofIsRightAdjoint (restrictToOver U)).homEquiv _ _).trans
        ((Adjunction.ofIsRightAdjoint (inclusionRestrict i)).homEquiv _ _))
          ((restrictToOver U).leftAdjoint.map
            (((Adjunction.ofIsRightAdjoint
              (inclusionRestrict i)).homEquiv _ _).symm
                (constantRestrictIso i M).hom)) =
        ((Adjunction.ofIsRightAdjoint (inclusionRestrict i)).homEquiv _ _)
          (((Adjunction.ofIsRightAdjoint (restrictToOver U)).homEquiv _ _)
            ((restrictToOver U).leftAdjoint.map
              (((Adjunction.ofIsRightAdjoint
                (inclusionRestrict i)).homEquiv _ _).symm
                  (constantRestrictIso i M).hom))) := rfl
  dsimp [overConstantSourceMap, overLeftAdjointCompIso]
  rw [Adjunction.homEquiv_naturality_right]
  erw [hleft'']
  erw [← Adjunction.homEquiv_unit]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  rw [Adjunction.comp_homEquiv]
  change
    (((Adjunction.ofIsRightAdjoint (restrictToOver U)).homEquiv _ _).trans
      ((Adjunction.ofIsRightAdjoint (inclusionRestrict i)).homEquiv _ _))
        ((restrictToOver U).leftAdjoint.map
          (((Adjunction.ofIsRightAdjoint
            (inclusionRestrict i)).homEquiv _ _).symm
              (constantRestrictIso i M).hom)) ≫
      (restrictToOverCompIso i).hom.app
        ((restrictToOver U).leftAdjoint.obj
          ((constantSheaf ((Opens.grothendieckTopology X).over U)
            AddCommGrpCat.{u}).obj M)) = _
  rw [htrans]
  erw [hamb]
  erw [hincl]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
omit globalSheafify overUSheafify overVSheafify
  overULocallyBijective overUSheafCompose
  overVLocallyBijective overVSheafCompose
  overUExt overVExt globalExt in
/-- The sheafified free-Yoneda source map along `V ⟶ U` is the canonical
over-site source map transported through the two representing isomorphisms. -/
theorem globalCohomologySourceFunctor_map :
    globalCohomologySourceFunctor.map i =
      (cohomologySourceIsoOverConstantSource V).hom ≫
        overConstantSourceMap i ↧(ULift ℤ) ≫
          (cohomologySourceIsoOverConstantSource U).inv := by
  let corepV := cohomologySourceCorepresentable V
  let overCorepV :=
    overConstantSourceCorepresentableForSections V
  let isoV := cohomologySourceIsoOverConstantSource V
  let corepU := cohomologySourceCorepresentable U
  let overCorepU :=
    overConstantSourceCorepresentableForSections U
  let isoU := cohomologySourceIsoOverConstantSource U
  have hglobal :
      corepV.homEquiv (globalCohomologySourceFunctor.map i) =
        (sectionsRestrict i).app (cohomologySource U)
          (corepU.homEquiv (𝟙 _)) := by
    dsimp [corepV, corepU,
      cohomologySourceCorepresentable,
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
  have hover :
      (sectionsAtType V).map
          (overConstantSourceMap i ↧(ULift ℤ))
          (overCorepV.homEquiv (𝟙 _)) =
        (sectionsRestrict i).app (overConstantSource U)
          (overCorepU.homEquiv (𝟙 _)) := by
    have hconstV
        (F : CategoryTheory.Sheaf
          ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u})
        (f : (constantSheaf ((Opens.grothendieckTopology X).over V)
            AddCommGrpCat.{u}).obj ↧(ULift ℤ) ⟶ F) :
        ((constantSheafAdj ((Opens.grothendieckTopology X).over V)
          AddCommGrpCat.{u} Over.mkIdTerminal).homEquiv _ _) f =
          (toSheafify ((Opens.grothendieckTopology X).over V)
              ((Functor.const (Over V)ᵒᵖ).obj
                (AddCommGrpCat.of (ULift ℤ))) ≫
            f.hom).app (.op (Over.mk (𝟙 V))) := by
      rfl
    have hconstU
        (F : CategoryTheory.Sheaf
          ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u})
        (f : (constantSheaf ((Opens.grothendieckTopology X).over U)
            AddCommGrpCat.{u}).obj ↧(ULift ℤ) ⟶ F) :
        ((constantSheafAdj ((Opens.grothendieckTopology X).over U)
          AddCommGrpCat.{u} Over.mkIdTerminal).homEquiv _ _) f =
          (toSheafify ((Opens.grothendieckTopology X).over U)
              ((Functor.const (Over U)ᵒᵖ).obj
                (AddCommGrpCat.of (ULift ℤ))) ≫
            f.hom).app (.op (Over.mk (𝟙 U))) := by
      rfl
    have hulift (A B : AddCommGrpCat.{u}) (f : A ⟶ B)
        (g : AddCommGrpCat.of (ULift ℤ) ⟶ A) :
        (AddCommGrpCat.uliftZMultiplesAddEquiv B).toEquiv (g ≫ f) =
          f ((AddCommGrpCat.uliftZMultiplesAddEquiv A).toEquiv g) := by
      change
        (AddCommGrpCat.coyonedaObjIsoForget.hom.app B) (g ≫ f) =
          ((CategoryTheory.forget AddCommGrpCat.{u}).map f)
            ((AddCommGrpCat.coyonedaObjIsoForget.hom.app A) g)
      convert ConcreteCategory.congr_hom
        (AddCommGrpCat.coyonedaObjIsoForget.hom.naturality f) g using 1 <;>
          rfl
    have hleft :=
      Adjunction.homEquiv_leftAdjointUniq_hom_app
        (Adjunction.ofIsRightAdjoint (restrictToOver V))
        (((Adjunction.ofIsRightAdjoint (inclusionRestrict i)).comp
          (Adjunction.ofIsRightAdjoint (restrictToOver U))).ofNatIsoRight
            (restrictToOverCompIso i))
        ((constantSheaf ((Opens.grothendieckTopology X).over V)
          AddCommGrpCat.{u}).obj ↧(ULift ℤ))
    have hleft' :
        ((Adjunction.ofIsRightAdjoint
            (restrictToOver V)).homEquiv _ _)
            ((overLeftAdjointCompIso i).hom.app
              ((constantSheaf ((Opens.grothendieckTopology X).over V)
                AddCommGrpCat.{u}).obj ↧(ULift ℤ))) =
          (((Adjunction.ofIsRightAdjoint (inclusionRestrict i)).comp
            (Adjunction.ofIsRightAdjoint (restrictToOver U))).ofNatIsoRight
              (restrictToOverCompIso i)).unit.app
                ((constantSheaf
                  ((Opens.grothendieckTopology X).over V)
                  AddCommGrpCat.{u}).obj ↧(ULift ℤ)) := hleft
    have hleft'' :
        ((Adjunction.ofIsRightAdjoint
            (restrictToOver V)).homEquiv
          ((constantSheaf ((Opens.grothendieckTopology X).over V)
            AddCommGrpCat.{u}).obj ↧(ULift ℤ))
          ((restrictToOver U).leftAdjoint.obj
            ((inclusionRestrict i).leftAdjoint.obj
              ((constantSheaf ((Opens.grothendieckTopology X).over V)
                AddCommGrpCat.{u}).obj ↧(ULift ℤ)))))
          ((overLeftAdjointCompIso i).hom.app
            ((constantSheaf ((Opens.grothendieckTopology X).over V)
              AddCommGrpCat.{u}).obj ↧(ULift ℤ))) =
        (((Adjunction.ofIsRightAdjoint (inclusionRestrict i)).comp
          (Adjunction.ofIsRightAdjoint (restrictToOver U))).ofNatIsoRight
            (restrictToOverCompIso i)).unit.app
              ((constantSheaf ((Opens.grothendieckTopology X).over V)
                AddCommGrpCat.{u}).obj ↧(ULift ℤ)) := hleft'
    have hamb :
        ((Adjunction.ofIsRightAdjoint (restrictToOver U)).homEquiv _ _)
            ((restrictToOver U).leftAdjoint.map
              (((Adjunction.ofIsRightAdjoint
                (inclusionRestrict i)).homEquiv _ _).symm
                  (constantRestrictIso i ↧(ULift ℤ)).hom)) =
          (((Adjunction.ofIsRightAdjoint
              (inclusionRestrict i)).homEquiv _ _).symm
                (constantRestrictIso i ↧(ULift ℤ)).hom) ≫
            ((Adjunction.ofIsRightAdjoint (restrictToOver U)).homEquiv _ _)
              (𝟙 _) := by
      rw [← Category.comp_id
        ((restrictToOver U).leftAdjoint.map
          (((Adjunction.ofIsRightAdjoint
            (inclusionRestrict i)).homEquiv _ _).symm
              (constantRestrictIso i ↧(ULift ℤ)).hom))]
      exact (Adjunction.ofIsRightAdjoint
        (restrictToOver U)).homEquiv_naturality_left _ _
    have hincl :
        ((Adjunction.ofIsRightAdjoint (inclusionRestrict i)).homEquiv _ _)
            ((((Adjunction.ofIsRightAdjoint
                (inclusionRestrict i)).homEquiv _ _).symm
                  (constantRestrictIso i ↧(ULift ℤ)).hom) ≫
              ((Adjunction.ofIsRightAdjoint (restrictToOver U)).homEquiv _ _)
                (𝟙 _)) =
          (constantRestrictIso i ↧(ULift ℤ)).hom ≫
            (inclusionRestrict i).map
              (((Adjunction.ofIsRightAdjoint
                (restrictToOver U)).homEquiv _ _) (𝟙 _)) := by
      rw [(Adjunction.ofIsRightAdjoint
        (inclusionRestrict i)).homEquiv_naturality_right]
      rw [Equiv.apply_symm_apply]
    have htrans :
        (((Adjunction.ofIsRightAdjoint (restrictToOver U)).homEquiv _ _).trans
          ((Adjunction.ofIsRightAdjoint (inclusionRestrict i)).homEquiv _ _))
            ((restrictToOver U).leftAdjoint.map
              (((Adjunction.ofIsRightAdjoint
                (inclusionRestrict i)).homEquiv _ _).symm
                  (constantRestrictIso i ↧(ULift ℤ)).hom)) =
          ((Adjunction.ofIsRightAdjoint (inclusionRestrict i)).homEquiv _ _)
            (((Adjunction.ofIsRightAdjoint (restrictToOver U)).homEquiv _ _)
              ((restrictToOver U).leftAdjoint.map
                (((Adjunction.ofIsRightAdjoint
                  (inclusionRestrict i)).homEquiv _ _).symm
                    (constantRestrictIso i ↧(ULift ℤ)).hom))) := rfl
    have hfull :
        toSheafify ((Opens.grothendieckTopology X).over V)
            ((Functor.const (Over V)ᵒᵖ).obj
              (AddCommGrpCat.of (ULift ℤ))) ≫
          ((((constantRestrictIso i ↧(ULift ℤ)).hom ≫
            (inclusionRestrict i).map
              (((Adjunction.ofIsRightAdjoint
                (restrictToOver U)).homEquiv _ _) (𝟙 _))) ≫
            (restrictToOverCompIso i).hom.app
              (overConstantSource U)).hom) =
        ((Functor.constCompWhiskeringLeftIso (Over V)ᵒᵖ
            (C := AddCommGrpCat.{u}) (Over.map i).op).inv.app
              (AddCommGrpCat.of (ULift ℤ)) ≫
          (Over.map i).op.whiskerLeft
            (toSheafify ((Opens.grothendieckTopology X).over U)
              ((Functor.const (Over U)ᵒᵖ).obj
                (AddCommGrpCat.of (ULift ℤ))))) ≫
          (((inclusionRestrict i).map
            (((Adjunction.ofIsRightAdjoint
              (restrictToOver U)).homEquiv _ _) (𝟙 _)) ≫
            (restrictToOverCompIso i).hom.app
              (overConstantSource U)).hom) := by
      change _ ≫ ((_ ≫ _) ≫ _) = (_ ≫ _) ≫ (_ ≫ _)
      simp only [← Category.assoc]
      rw [toSheafify_constantRestrictIso]
    rw [← overCorepV.homEquiv_comp, Category.id_comp]
    change
      (overConstantSourceCorepresentable V).homEquiv
          (overConstantSourceMap i ↧(ULift ℤ)) =
        (overConstantSource U).obj.map i.op
          ((overConstantSourceCorepresentable U).homEquiv
            (𝟙 _))
    dsimp [overConstantSourceCorepresentable,
      overConstantSourceMap, overLeftAdjointCompIso]
    rw [Adjunction.homEquiv_naturality_right]
    erw [hleft'']
    erw [← Adjunction.homEquiv_unit]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    rw [Adjunction.comp_homEquiv]
    dsimp only [Equiv.trans_apply]
    change
      (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv
        (((constantSheafAdj
        ((Opens.grothendieckTopology X).over V)
        AddCommGrpCat.{u} Over.mkIdTerminal).homEquiv _ _)
          (((Adjunction.ofIsRightAdjoint
              (inclusionRestrict i)).homEquiv _ _)
            (((Adjunction.ofIsRightAdjoint
                (restrictToOver U)).homEquiv _ _)
              ((restrictToOver U).leftAdjoint.map
                (((Adjunction.ofIsRightAdjoint
                  (inclusionRestrict i)).homEquiv _ _).symm
                    (constantRestrictIso i ↧(ULift ℤ)).hom))) ≫
              (restrictToOverCompIso i).hom.app
                ((restrictToOver U).leftAdjoint.obj
                  ((constantSheaf
                    ((Opens.grothendieckTopology X).over U)
                    AddCommGrpCat.{u}).obj ↧(ULift ℤ))))) = _
    erw [hamb]
    erw [hincl]
    erw [hconstV]
    erw [hconstU]
    rw [NatTrans.congr_app hfull (.op (Over.mk (𝟙 V)))]
    simp only [NatTrans.comp_app,
      Functor.constCompWhiskeringLeftIso_inv_app_app,
      Functor.whiskerLeft_app]
    erw [hulift]
    erw [hulift]
    erw [hulift]
    let k : (Over.map i).obj (Over.mk (𝟙 V)) ⟶ Over.mk (𝟙 U) :=
      Over.homMk i
    have hn :=
      (toSheafify ((Opens.grothendieckTopology X).over U)
          ((Functor.const (Over U)ᵒᵖ).obj
            (AddCommGrpCat.of (ULift ℤ))) ≫
        ((Adjunction.ofIsRightAdjoint (restrictToOver U)).unit.app
          ((constantSheaf ((Opens.grothendieckTopology X).over U)
            AddCommGrpCat.{u}).obj ↧(ULift ℤ))).hom).naturality k.op
    have hn' := congrArg
      (fun q => (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv q) hn
    simp only [Functor.const_obj_map] at hn'
    erw [hulift] at hn'
    erw [hulift] at hn'
    erw [hulift] at hn'
    exact hn'
  apply corepV.homEquiv.injective
  rw [corepV.homEquiv_comp]
  have huniq :
      corepV.homEquiv isoV.hom = overCorepV.homEquiv (𝟙 _) := by
    change corepV.homEquiv
      (corepV.homEquiv.symm (overCorepV.homEquiv (𝟙 _))) = _
    exact Equiv.apply_symm_apply _ _
  rw [huniq]
  rw [Functor.map_comp_apply]
  rw [hglobal]
  rw [hover]
  rw [← NatTrans.naturality_apply]
  have huniqU :
      corepU.homEquiv isoU.hom = overCorepU.homEquiv (𝟙 _) := by
    change corepU.homEquiv
      (corepU.homEquiv.symm (overCorepU.homEquiv (𝟙 _))) = _
    exact Equiv.apply_symm_apply _ _
  rw [← huniqU]
  rw [← corepU.homEquiv_comp]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Under `HPrimeEquivHOver`, the intrinsic over-site restriction agrees with
the restriction map of `Sheaf.cohomologyPresheafFunctor`. -/
theorem HPrimeEquivHOver_map
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) (n : ℕ) (x : CategoryTheory.Sheaf.H' G n U) :
    HOverMap i G n (HPrimeEquivHOver U G n x) =
      HPrimeEquivHOver V G n
        (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) n).obj G).map i.op x) := by
  let : (inclusionRestrict i).Additive :=
    (inclusionRestrict i).additive_of_preserves_binary_products
  let : (restrictToOver U).leftAdjoint.Additive :=
    (restrictToOver U).leftAdjoint.additive_of_preserves_binary_products
  let : (restrictToOver U).Additive :=
    (restrictToOver U).additive_of_preserves_binary_products
  let : (restrictToOver V).leftAdjoint.Additive :=
    (restrictToOver V).leftAdjoint.additive_of_preserves_binary_products
  let : (restrictToOver V).Additive :=
    (restrictToOver V).additive_of_preserves_binary_products
  simp [HOverMap, HPrimeEquivHOver,
    cohomologySourceExtIso, overExtEquiv]
  simp only [Adjunction.extEquiv_apply]
  rw [Abelian.Ext.mapExactFunctor_comp]
  rw [Abelian.Ext.mapExactFunctor_mk₀]
  rw [← Abelian.Ext.comp_mapExactFunctor]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [Abelian.Ext.mapExactFunctor_comp_mk₀_natTransApp]
  simp only [Abelian.Ext.mk₀_comp_mk₀_assoc]
  have hm :
      (constantRestrictIso i ↧(ULift ℤ)).hom ≫
          (inclusionRestrict i).map
            ((Adjunction.ofIsRightAdjoint (restrictToOver U)).unit.app
              ((constantSheaf
                ((Opens.grothendieckTopology X).over U)
                AddCommGrpCat.{u}).obj ↧(ULift ℤ))) ≫
          (restrictToOverCompIso i).hom.app
            ((restrictToOver U).leftAdjoint.obj
              ((constantSheaf
                ((Opens.grothendieckTopology X).over U)
                AddCommGrpCat.{u}).obj ↧(ULift ℤ))) =
        (Adjunction.ofIsRightAdjoint (restrictToOver V)).unit.app
            ((constantSheaf
              ((Opens.grothendieckTopology X).over V)
              AddCommGrpCat.{u}).obj ↧(ULift ℤ)) ≫
          (restrictToOver V).map
            (overConstantSourceMap i ↧(ULift ℤ)) := by
    simpa [Adjunction.homEquiv_apply] using
      (overConstantSourceMap_homEquiv
        (X := X) i (AddCommGrpCat.of (ULift ℤ))).symm
  rw [hm]
  rw [← Abelian.Ext.mk₀_comp_mk₀_assoc]
  congr 1
  rw [← Abelian.Ext.mapExactFunctor_mk₀]
  rw [← Abelian.Ext.mapExactFunctor_comp]
  congr 1
  change
    (Abelian.Ext.mk₀ (overConstantSourceMap i ↧(ULift ℤ))).comp
      ((((Abelian.extFunctor n).mapIso
          (cohomologySourceIsoOverConstantSource U).op).symm.app
            G).addCommGroupIsoToAddEquiv x)
        (zero_add n) =
      (((Abelian.extFunctor n).mapIso
          (cohomologySourceIsoOverConstantSource V).op).symm.app
            G).addCommGroupIsoToAddEquiv
        ((((Abelian.extFunctor n).map
          (globalCohomologySourceFunctor.map i).op).app G) x)
  rw [globalCohomologySourceFunctor_map (X := X) i]
  simp
  change
    (Abelian.Ext.mk₀ (overConstantSourceMap i ↧(ULift ℤ))).comp
        ((Abelian.Ext.mk₀
          (cohomologySourceIsoOverConstantSource U).inv).comp
            x (zero_add n)) (zero_add n) =
      (Abelian.Ext.mk₀
        (cohomologySourceIsoOverConstantSource V).inv).comp
          ((Abelian.Ext.mk₀
            (cohomologySourceIsoOverConstantSource V).hom).comp
              ((Abelian.Ext.mk₀
                (overConstantSourceMap i ↧(ULift ℤ))).comp
                  ((Abelian.Ext.mk₀
                    (cohomologySourceIsoOverConstantSource U).inv).comp
                      x (zero_add n)) (zero_add n))
              (zero_add n))
          (zero_add n)
  simp only [Abelian.Ext.mk₀_comp_mk₀_assoc,
    Iso.inv_hom_id_assoc]

end OpenComparison

end CategoryTheory.Sheaf.OpenCohomology
