/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Spectral.Basic

public section

/-!
# Filtered colimits and sections on compact opens

This file proves that evaluation on a compact open preserves filtered colimits
of sheaves valued in a suitable concrete category.  The proof computes a sheaf
colimit by sheafifying the pointwise presheaf colimit.  Compactness reduces
local equality and local representability to finite data, which can be moved to
one stage of the filtered diagram.

The space and coefficient universes are independent.  The implementation uses
a same-size indexing category and `UnivLE` internally so that the required
presheaf, sheaf, and evaluated colimits are inferred by the current
category-theory API.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits ConcreteCategory Opposite
open TopologicalSpace

universe u v

namespace SheafCohomology.CompactOpenSections

variable {X : Type u} [TopologicalSpace X]
variable {C : Type (v + 1)} [Category.{v} C]
variable {FC : C → C → Type*} {CC : C → Type v}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)]
variable [instCC : ConcreteCategory C FC] [HasColimitsOfSize.{v, v} C]
variable [HasLimitsOfSize.{u, u} C]
variable [PreservesFilteredColimits (forget C)]
variable [PreservesLimitsOfSize.{u, u} (forget C)]
variable [instReflectsIsomorphisms : (forget C).ReflectsIsomorphisms]

/-- Evaluation of a `C`-valued sheaf on an open set. -/
abbrev sectionsOf (U : Opens X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) C ⥤
      C :=
  (CategoryTheory.sheafSections
    (Opens.grothendieckTopology X) C).obj (op U)

/-- Evaluation of an `AddCommGrpCat`-valued sheaf on an open set.

This retains the original additive API while `sectionsOf` supplies the generic
concrete-category evaluator used by the filtered-colimit proof. -/
abbrev sections (U : Opens X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v} ⥤
      AddCommGrpCat.{v} :=
  sectionsOf U

local notation "sections" => sectionsOf

variable [UnivLE.{u, v}]
variable [HasWeakSheafify
  (Opens.grothendieckTopology X) C]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective
  C]
variable {I : Type v} [SmallCategory I] [IsFiltered I]
variable (F : I ⥤ CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) C)

/-- The pointwise presheaf colimit underlying the explicit sheaf colimit. -/
abbrev underlyingPresheafColimit :
    (Opens X)ᵒᵖ ⥤ C :=
  colimit (F ⋙ CategoryTheory.sheafToPresheaf
    (Opens.grothendieckTopology X) C)

/-- The sheafification cocone built from the pointwise presheaf colimit. -/
abbrev explicitSheafColimitCocone : Cocone F :=
  CategoryTheory.Sheaf.sheafifyCocone
    (colimit.cocone
      (F ⋙ CategoryTheory.sheafToPresheaf
        (Opens.grothendieckTopology X) C))

/-- The explicit sheafification cocone is colimiting. -/
@[expose] def explicitSheafColimitCoconeIsColimit :
    IsColimit (explicitSheafColimitCocone F) :=
  CategoryTheory.Sheaf.isColimitSheafifyCocone
    (colimit.cocone
      (F ⋙ CategoryTheory.sheafToPresheaf
        (Opens.grothendieckTopology X) C))
    (colimit.isColimit
      (F ⋙ CategoryTheory.sheafToPresheaf
        (Opens.grothendieckTopology X) C))

/-- The unique isomorphism from the explicit sheafification model to the
chosen sheaf colimit. -/
@[expose] def explicitSheafColimitIso :
    (presheafToSheaf (Opens.grothendieckTopology X)
        C).obj (underlyingPresheafColimit F) ≅ colimit F :=
  (explicitSheafColimitCoconeIsColimit F).coconePointUniqueUpToIso
    (colimit.isColimit F)

/-- The direct comparison from the colimit of sections to sections of the
explicit sheafification model. -/
@[expose] def explicitSectionsComparison (U : Opens X) :
    colimit (F ⋙ sections U) ⟶
      (sheafify (Opens.grothendieckTopology X)
        (underlyingPresheafColimit F)).obj (op U) :=
  (colimitObjIsoColimitCompEvaluation
      (F ⋙ CategoryTheory.sheafToPresheaf
        (Opens.grothendieckTopology X) C) (op U)).inv ≫
    (toSheafify (Opens.grothendieckTopology X)
      (underlyingPresheafColimit F)).app (op U)

/-- The direct comparison transported to the chosen sheaf colimit. -/
@[expose] def transportedExplicitSectionsComparison (U : Opens X) :
    colimit (F ⋙ sections U) ⟶ sections U |>.obj (colimit F) :=
  explicitSectionsComparison F U ≫
    (sections U).map (explicitSheafColimitIso F).hom

omit [IsFiltered I] [UnivLE.{u, v}]
  [HasLimitsOfSize.{u, u} C]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    C] in
@[reassoc]
theorem colimit_ι_explicitSectionsComparison (U : Opens X) (i : I) :
    colimit.ι
          ((F ⋙ CategoryTheory.sheafToPresheaf
              (Opens.grothendieckTopology X) C) ⋙
            (evaluation (Opens X)ᵒᵖ C).obj (op U)) i ≫
        (colimitObjIsoColimitCompEvaluation
          (F ⋙ CategoryTheory.sheafToPresheaf
            (Opens.grothendieckTopology X) C) (op U)).inv ≫
        (toSheafify (Opens.grothendieckTopology X)
          (underlyingPresheafColimit F)).app (op U) =
      ((explicitSheafColimitCocone F).ι.app i).hom.app (op U) := by
  rw [← Category.assoc, colimitObjIsoColimitCompEvaluation_ι_inv]
  exact NatTrans.congr_app
    (CategoryTheory.Sheaf.sheafifyCocone_ι_app_val
      (colimit.cocone
        (F ⋙ CategoryTheory.sheafToPresheaf
          (Opens.grothendieckTopology X) C)) i)
    (op U) |>.symm

omit [IsFiltered I] [UnivLE.{u, v}]
  [HasLimitsOfSize.{u, u} C]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    C] in
theorem explicitSheafColimitCocone_ι_iso_hom_app
    (U : Opens X) (i : I) :
    ((explicitSheafColimitCocone F).ι.app i).hom.app (op U) ≫
        (explicitSheafColimitIso F).hom.hom.app (op U) =
      (colimit.ι F i).hom.app (op U) := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (explicitSheafColimitCoconeIsColimit F) (colimit.isColimit F) i
  exact NatTrans.congr_app (congr_arg (fun f => f.hom) h) (op U)

omit [IsFiltered I] [UnivLE.{u, v}]
  [HasLimitsOfSize.{u, u} C]
  [PreservesFilteredColimits (forget C)]
  [PreservesLimitsOfSize.{u, u} (forget C)]
  instReflectsIsomorphisms
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    C] in
/-- The transported direct comparison is the canonical `colimit.post`
comparison. -/
theorem transportedExplicitSectionsComparison_eq (U : Opens X) :
    transportedExplicitSectionsComparison F U =
      colimit.post F (sections U) := by
  apply colimit.hom_ext
  intro i
  unfold transportedExplicitSectionsComparison explicitSectionsComparison
  rw [← Category.assoc]
  change
    (colimit.ι
          ((F ⋙ CategoryTheory.sheafToPresheaf
              (Opens.grothendieckTopology X) C) ⋙
            (evaluation (Opens X)ᵒᵖ C).obj (op U)) i ≫
        (colimitObjIsoColimitCompEvaluation
          (F ⋙ CategoryTheory.sheafToPresheaf
            (Opens.grothendieckTopology X) C) (op U)).inv ≫
        (toSheafify (Opens.grothendieckTopology X)
          (underlyingPresheafColimit F)).app (op U)) ≫
        (explicitSheafColimitIso F).hom.hom.app (op U) =
      colimit.ι (F ⋙ sections U) i ≫ colimit.post F (sections U)
  rw [colimit_ι_explicitSectionsComparison]
  calc
    _ = (colimit.ι F i).hom.app (op U) :=
      explicitSheafColimitCocone_ι_iso_hom_app F U i
    _ = _ := (colimit.ι_post F (sections U) i).symm

omit [IsFiltered I] [UnivLE.{u, v}]
  [HasLimitsOfSize.{u, u} C]
  [PreservesFilteredColimits (forget C)]
  [PreservesLimitsOfSize.{u, u} (forget C)]
  instReflectsIsomorphisms
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    C] in
/-- Naturality of the direct comparison with respect to restriction of
sections. -/
theorem explicitSectionsComparison_ι_naturality
    {V U : Opens X} (f : V ⟶ U) (i : I)
    (s : ToType ((F.obj i).obj.obj (op U))) :
    explicitSectionsComparison F V
        (colimit.ι (F ⋙ sections V) i ((F.obj i).obj.map f.op s)) =
      (sheafify (Opens.grothendieckTopology X)
        (underlyingPresheafColimit F)).map f.op
        (explicitSectionsComparison F U
          (colimit.ι (F ⋙ sections U) i s)) := by
  have hV : colimit.ι
        ((F ⋙ CategoryTheory.sheafToPresheaf
            (Opens.grothendieckTopology X) C) ⋙
          (evaluation (Opens X)ᵒᵖ C).obj (op V)) i ≫
      explicitSectionsComparison F V =
        ((explicitSheafColimitCocone F).ι.app i).hom.app (op V) := by
    simpa only [explicitSectionsComparison] using
      colimit_ι_explicitSectionsComparison F V i
  have hU : colimit.ι
        ((F ⋙ CategoryTheory.sheafToPresheaf
            (Opens.grothendieckTopology X) C) ⋙
          (evaluation (Opens X)ᵒᵖ C).obj (op U)) i ≫
      explicitSectionsComparison F U =
        ((explicitSheafColimitCocone F).ι.app i).hom.app (op U) := by
    simpa only [explicitSectionsComparison] using
      colimit_ι_explicitSectionsComparison F U i
  have hV' : colimit.ι (F ⋙ sections V) i ≫
      explicitSectionsComparison F V =
        ((explicitSheafColimitCocone F).ι.app i).hom.app (op V) := hV
  have hU' : colimit.ι (F ⋙ sections U) i ≫
      explicitSectionsComparison F U =
        ((explicitSheafColimitCocone F).ι.app i).hom.app (op U) := hU
  rw [show explicitSectionsComparison F V
      (colimit.ι (F ⋙ sections V) i ((F.obj i).obj.map f.op s)) =
        ((explicitSheafColimitCocone F).ι.app i).hom.app
          (op V) ((F.obj i).obj.map f.op s) by
            rw [← ConcreteCategory.comp_apply]
            exact congr_hom hV' _]
  rw [show explicitSectionsComparison F U
      (colimit.ι (F ⋙ sections U) i s) =
        ((explicitSheafColimitCocone F).ι.app i).hom.app (op U) s by
          rw [← ConcreteCategory.comp_apply]
          exact congr_hom hU' _]
  have hn := congr_hom
    (((explicitSheafColimitCocone F).ι.app i).hom.naturality f.op) s
  simp only [ConcreteCategory.comp_apply] at hn
  exact hn

/-- A section-colimit element viewed in the pointwise presheaf colimit. -/
@[expose] def explicitPresheafSectionRepresentative (U : Opens X)
    (s : ToType (colimit (F ⋙ sections U))) :
    ToType ((underlyingPresheafColimit F).obj (op U)) :=
  (colimitObjIsoColimitCompEvaluation
    (F ⋙ CategoryTheory.sheafToPresheaf
      (Opens.grothendieckTopology X) C) (op U)).inv s

omit [IsFiltered I] [UnivLE.{u, v}]
  [HasLimitsOfSize.{u, u} C]
  [PreservesFilteredColimits (forget C)]
  [PreservesLimitsOfSize.{u, u} (forget C)]
  instReflectsIsomorphisms
  [HasWeakSheafify (Opens.grothendieckTopology X) C]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    C] in
@[simp]
theorem explicitPresheafSectionRepresentative_ι (U : Opens X) (i : I)
    (s : ToType ((F.obj i).obj.obj (op U))) :
    explicitPresheafSectionRepresentative F U
        (colimit.ι (F ⋙ sections U) i s) =
      (colimit.ι
        (F ⋙ CategoryTheory.sheafToPresheaf
          (Opens.grothendieckTopology X) C) i).app (op U) s := by
  have h := colimitObjIsoColimitCompEvaluation_ι_inv
    (F ⋙ CategoryTheory.sheafToPresheaf
      (Opens.grothendieckTopology X) C) i (op U)
  change colimit.ι (F ⋙ sections U) i ≫
      (colimitObjIsoColimitCompEvaluation
        (F ⋙ CategoryTheory.sheafToPresheaf
          (Opens.grothendieckTopology X) C) (op U)).inv = _ at h
  simpa only [explicitPresheafSectionRepresentative,
    ConcreteCategory.comp_apply] using congr_hom h s

omit [IsFiltered I] [UnivLE.{u, v}]
  [HasLimitsOfSize.{u, u} C]
  [PreservesFilteredColimits (forget C)]
  [PreservesLimitsOfSize.{u, u} (forget C)]
  instReflectsIsomorphisms
  [HasWeakSheafify (Opens.grothendieckTopology X) C]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    C] in
@[simp]
theorem underlyingPresheafColimit_map_representative_ι
    (U : Opens X) (i : I) (s : ToType ((F.obj i).obj.obj (op U)))
    {V : Opens X} (f : V ⟶ U) :
    (underlyingPresheafColimit F).map f.op
        (explicitPresheafSectionRepresentative F U
          (colimit.ι (F ⋙ sections U) i s)) =
      (colimit.ι
        (F ⋙ CategoryTheory.sheafToPresheaf
          (Opens.grothendieckTopology X) C) i).app (op V)
        ((F.obj i).obj.map f.op s) := by
  rw [explicitPresheafSectionRepresentative_ι]
  have h := congr_hom ((colimit.ι
      (F ⋙ CategoryTheory.sheafToPresheaf
        (Opens.grothendieckTopology X) C) i).naturality f.op).symm s
  simp only [ConcreteCategory.comp_apply] at h
  exact h

omit [UnivLE.{u, v}]
  [HasLimitsOfSize.{u, u} C]
  [PreservesLimitsOfSize.{u, u} (forget C)]
  instReflectsIsomorphisms
  [HasWeakSheafify (Opens.grothendieckTopology X) C]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective
    C] in
/-- Equality of two restrictions in the pointwise colimit is witnessed at one
later stage. -/
theorem exists_stage_of_section_restriction_eq
    (U : Opens X) (i : I)
    (s t : ToType ((F.obj i).obj.obj (op U)))
    {V : Opens X} (f : V ⟶ U)
    (h : (underlyingPresheafColimit F).map f.op
          (explicitPresheafSectionRepresentative F U
            (colimit.ι (F ⋙ sections U) i s)) =
        (underlyingPresheafColimit F).map f.op
          (explicitPresheafSectionRepresentative F U
            (colimit.ι (F ⋙ sections U) i t))) :
    ∃ (k : I) (g : i ⟶ k),
      (F ⋙ sections V).map g ((F.obj i).obj.map f.op s) =
        (F ⋙ sections V).map g ((F.obj i).obj.map f.op t) := by
  rw [underlyingPresheafColimit_map_representative_ι,
    underlyingPresheafColimit_map_representative_ι] at h
  let D := F ⋙ CategoryTheory.sheafToPresheaf
    (Opens.grothendieckTopology X) C
  let E := ((evaluation (Opens X)ᵒᵖ C).obj (op V)).mapCocone
    (colimit.cocone D)
  have hE : IsColimit E := isColimitOfPreserves
    ((evaluation (Opens X)ᵒᵖ C).obj (op V))
    (colimit.isColimit D)
  exact (hE.eq_iff' ((F.obj i).obj.map f.op s)
    ((F.obj i).obj.map f.op t)).mp h

omit [IsFiltered I] [UnivLE.{u, v}]
  [HasLimitsOfSize.{u, u} C]
  [PreservesFilteredColimits (forget C)]
  [PreservesLimitsOfSize.{u, u} (forget C)]
  instReflectsIsomorphisms in
/-- Equality after sheafification is witnessed on an open neighborhood of
each point. -/
theorem exists_open_restriction_eq_of_explicitComparison_eq
    (U : Opens X) {s t : ToType (colimit (F ⋙ sections U))}
    (h : explicitSectionsComparison F U s =
      explicitSectionsComparison F U t) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (f : V ⟶ U), x ∈ V ∧
      (underlyingPresheafColimit F).map f.op
          (explicitPresheafSectionRepresentative F U s) =
        (underlyingPresheafColimit F).map f.op
          (explicitPresheafSectionRepresentative F U t) := by
  have hsieve : Presheaf.equalizerSieve
        (F := underlyingPresheafColimit F)
        (explicitPresheafSectionRepresentative F U s)
        (explicitPresheafSectionRepresentative F U t) ∈
      Opens.grothendieckTopology X U := by
    apply Presheaf.equalizerSieve_mem
      (Opens.grothendieckTopology X)
      (toSheafify (Opens.grothendieckTopology X)
        (underlyingPresheafColimit F))
    simpa only [explicitSectionsComparison,
      explicitPresheafSectionRepresentative,
      ConcreteCategory.comp_apply] using h
  rw [Opens.mem_grothendieckTopology] at hsieve
  obtain ⟨V, f, hf, hxV⟩ := hsieve x hx
  exact ⟨V, f, hxV, hf⟩

omit [UnivLE.{u, v}] in
/-- The direct comparison is injective on a compact open. -/
theorem explicitSectionsComparison_injective
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    Function.Injective (explicitSectionsComparison F U) := by
  classical
  intro s t h
  obtain ⟨i, a, ha⟩ := Concrete.colimit_exists_rep (F ⋙ sections U) s
  obtain ⟨j, b, hb⟩ := Concrete.colimit_exists_rep (F ⋙ sections U) t
  let k : I := IsFiltered.max i j
  let fi : i ⟶ k := IsFiltered.leftToMax i j
  let fj : j ⟶ k := IsFiltered.rightToMax i j
  let a' : ToType ((F.obj k).obj.obj (op U)) := (F ⋙ sections U).map fi a
  let b' : ToType ((F.obj k).obj.obj (op U)) := (F ⋙ sections U).map fj b
  have ha' : colimit.ι (F ⋙ sections U) k a' = s := by
    calc
      _ = ((F ⋙ sections U).map fi ≫ colimit.ι (F ⋙ sections U) k) a := by
        simp only [a', ConcreteCategory.comp_apply]
      _ = colimit.ι (F ⋙ sections U) i a :=
        congr_hom (colimit.w (F ⋙ sections U) fi) a
      _ = s := ha
  have hb' : colimit.ι (F ⋙ sections U) k b' = t := by
    calc
      _ = ((F ⋙ sections U).map fj ≫ colimit.ι (F ⋙ sections U) k) b := by
        simp only [b', ConcreteCategory.comp_apply]
      _ = colimit.ι (F ⋙ sections U) j b :=
        congr_hom (colimit.w (F ⋙ sections U) fj) b
      _ = t := hb
  rw [← ha', ← hb'] at h ⊢
  choose V f hx heq using fun x : U =>
    exists_open_restriction_eq_of_explicitComparison_eq F U h x.1 x.2
  have hcover : (U : Set X) ⊆ ⋃ (x : U), (V x : Set X) := by
    intro x hxU
    exact Set.mem_iUnion.mpr ⟨⟨x, hxU⟩, hx ⟨x, hxU⟩⟩
  obtain ⟨S, hS⟩ := hU.elim_finite_subcover
    (fun x : U => (V x : Set X)) (fun x => (V x).2) hcover
  have hstage : ∀ x : U, ∃ (m : I) (g : k ⟶ m),
      (F ⋙ sections (V x)).map g ((F.obj k).obj.map (f x).op a') =
        (F ⋙ sections (V x)).map g
          ((F.obj k).obj.map (f x).op b') := by
    intro x
    exact exists_stage_of_section_restriction_eq F U k a' b' (f x) (heq x)
  choose m g hg using hstage
  let O : Finset I := insert k (S.image m)
  have hkO : k ∈ O := by simp [O]
  have hmO (x : U) (hxS : x ∈ S) : m x ∈ O := by
    simp only [O, Finset.mem_insert, Finset.mem_image]
    exact Or.inr ⟨x, hxS, rfl⟩
  let H : Finset (Σ' (A B : I) (_ : A ∈ O) (_ : B ∈ O), A ⟶ B) :=
    S.attach.image fun x => ⟨k, m x.1, hkO, hmO x.1 x.2, g x.1⟩
  let l : I := IsFiltered.sup O H
  let p : k ⟶ l := IsFiltered.toSup O H hkO
  let q (x : {x // x ∈ S}) : m x ⟶ l :=
    IsFiltered.toSup O H (hmO x x.2)
  have hp (x : {x // x ∈ S}) : g x ≫ q x = p := by
    apply IsFiltered.toSup_commutes O H hkO (hmO x x.2)
    simp only [H, Finset.mem_image]
    exact ⟨x, Finset.mem_attach S x, rfl⟩
  apply ((colimit.isColimit (F ⋙ sections U)).eq_iff' a' b').2
  refine ⟨l, p, ?_⟩
  have hcoverOpen : U ≤ ⨆ y : {x // x ∈ S}, V y.1 := by
    intro x hxU
    rw [Opens.mem_iSup]
    obtain ⟨y, hyS, hxy⟩ := Set.mem_iUnion₂.mp (hS hxU)
    exact ⟨⟨y, hyS⟩, hxy⟩
  apply TopCat.Sheaf.eq_of_locally_eq'
    (X := TopCat.of X) (F.obj l)
    (fun y : {x // x ∈ S} => V y.1) U
    (fun y => f y.1) hcoverOpen
  intro yS
  let y : U := yS.1
  have hpU : (F ⋙ sections U).map p = (F.map p).hom.app (op U) := rfl
  rw [hpU]
  change
    (F.obj l).obj.map (f y).op ((F.map p).hom.app (op U) a') =
      (F.obj l).obj.map (f y).op ((F.map p).hom.app (op U) b')
  calc
    (F.obj l).obj.map (f y).op ((F.map p).hom.app (op U) a') =
      (F.map p).hom.app (op (V y)) ((F.obj k).obj.map (f y).op a') := by
        simpa only [ConcreteCategory.comp_apply] using
          (congr_hom ((F.map p).hom.naturality (f y).op) a').symm
    _ = (F.map (q yS)).hom.app (op (V y))
        ((F.map (g y)).hom.app (op (V y))
          ((F.obj k).obj.map (f y).op a')) := by
        rw [← hp yS, F.map_comp]
        change (((F.map (g y)).hom.app (op (V y)) ≫
          (F.map (q yS)).hom.app (op (V y)))
            ((F.obj k).obj.map (f y).op a')) = _
        rw [ConcreteCategory.comp_apply]
    _ = (F.map (q yS)).hom.app (op (V y))
        ((F.map (g y)).hom.app (op (V y))
          ((F.obj k).obj.map (f y).op b')) := by
        exact _root_.congr_arg ((F.map (q yS)).hom.app (op (V y))) (hg y)
    _ = (F.map p).hom.app (op (V y)) ((F.obj k).obj.map (f y).op b') := by
        rw [← hp yS, F.map_comp]
        change _ = (((F.map (g y)).hom.app (op (V y)) ≫
          (F.map (q yS)).hom.app (op (V y)))
            ((F.obj k).obj.map (f y).op b'))
        rw [ConcreteCategory.comp_apply]
    _ = (F.obj l).obj.map (f y).op ((F.map p).hom.app (op U) b') := by
        simpa only [ConcreteCategory.comp_apply] using
          congr_hom ((F.map p).hom.naturality (f y).op) b'

omit [UnivLE.{u, v}] [IsFiltered I]
  [HasLimitsOfSize.{u, u} C]
  [PreservesFilteredColimits (forget C)]
  [PreservesLimitsOfSize.{u, u} (forget C)]
  instReflectsIsomorphisms in
/-- Every section of the explicit sheaf colimit is locally represented by a
section-colimit element on a compact open neighborhood. -/
theorem exists_compact_open_local_preimage [PrespectralSpace X]
    (U : Opens X)
    (s : ToType ((sheafify (Opens.grothendieckTopology X)
      (underlyingPresheafColimit F)).obj (op U)))
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (f : V ⟶ U), x ∈ V ∧ IsCompact (V : Set X) ∧
      ∃ t : ToType (colimit (F ⋙ sections V)),
        explicitSectionsComparison F V t =
          (sheafify (Opens.grothendieckTopology X)
            (underlyingPresheafColimit F)).map f.op s := by
  let T := toSheafify (Opens.grothendieckTopology X)
    (underlyingPresheafColimit F)
  have hsieve := CategoryTheory.Presheaf.imageSieve_mem
    (Opens.grothendieckTopology X) T s
  rw [Opens.mem_grothendieckTopology] at hsieve
  obtain ⟨V, iVU, ⟨t, ht⟩, hxV⟩ := hsieve x hx
  obtain ⟨W, ⟨hWopen, hWcompact⟩, hxW, hWV⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hxV V.2
  let W' : Opens X := ⟨W, hWopen⟩
  let g : W' ⟶ V := homOfLE hWV
  let f : W' ⟶ U := g ≫ iVU
  let e := colimitObjIsoColimitCompEvaluation
    (F ⋙ CategoryTheory.sheafToPresheaf
      (Opens.grothendieckTopology X) C) (op W')
  let a : ToType ((underlyingPresheafColimit F).obj (op W')) :=
    (underlyingPresheafColimit F).map g.op t
  let c : ToType (colimit (F ⋙ sections W')) := e.hom a
  refine ⟨W', f, hxW, hWcompact, c, ?_⟩
  change (e.inv ≫ T.app (op W')) (e.hom a) = _
  rw [ConcreteCategory.comp_apply]
  rw [e.hom_inv_id_apply]
  change T.app (op W')
      ((underlyingPresheafColimit F).map g.op t) = _
  rw [← ConcreteCategory.comp_apply, T.naturality,
    ConcreteCategory.comp_apply, ht]
  rw [← ConcreteCategory.comp_apply,
    ← (sheafify (Opens.grothendieckTopology X)
      (underlyingPresheafColimit F)).map_comp]
  rfl

omit [UnivLE.{u, v}] in
/-- The direct comparison is surjective on a compact open of a prespectral,
quasi-separated space. -/
theorem explicitSectionsComparison_surjective
    [PrespectralSpace X] [QuasiSeparatedSpace X]
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    Function.Surjective (explicitSectionsComparison F U) := by
  classical
  intro s
  choose V f hxV hVcompact c hc using fun x : U =>
    exists_compact_open_local_preimage F U s x.1 x.2
  have hcover : (U : Set X) ⊆ ⋃ x : U, (V x : Set X) := by
    intro x hxU
    exact Set.mem_iUnion.mpr ⟨⟨x, hxU⟩, hxV ⟨x, hxU⟩⟩
  obtain ⟨S, hS⟩ := hU.elim_finite_subcover
    (fun x : U => (V x : Set X)) (fun x => (V x).2) hcover
  have hrep : ∀ x : U,
      ∃ (i : I) (a : ToType ((F.obj i).obj.obj (op (V x)))),
        colimit.ι (F ⋙ sections (V x)) i a = c x := by
    intro x
    exact Concrete.colimit_exists_rep (F ⋙ sections (V x)) (c x)
  choose i a ha using hrep
  let i₀ : I := Classical.choice IsFiltered.nonempty
  let O : Finset I := insert i₀ (S.image i)
  have hiO (x : U) (hxS : x ∈ S) : i x ∈ O := by
    simp only [O, Finset.mem_insert, Finset.mem_image]
    exact Or.inr ⟨x, hxS, rfl⟩
  let H : Finset (Σ' (A B : I) (_ : A ∈ O) (_ : B ∈ O), A ⟶ B) := ∅
  let k : I := IsFiltered.sup O H
  let p (x : {x // x ∈ S}) : i x.1 ⟶ k :=
    IsFiltered.toSup O H (hiO x.1 x.2)
  let b (x : {x // x ∈ S}) :
      ToType ((F.obj k).obj.obj (op (V x.1))) :=
    (F ⋙ sections (V x.1)).map (p x) (a x.1)
  have hbcolim (x : {x // x ∈ S}) :
      colimit.ι (F ⋙ sections (V x.1)) k (b x) = c x.1 := by
    calc
      _ = colimit.ι (F ⋙ sections (V x.1)) (i x.1) (a x.1) := by
        simpa only [b, ConcreteCategory.comp_apply] using
          congr_hom (colimit.w (F ⋙ sections (V x.1)) (p x)) (a x.1)
      _ = _ := ha x.1
  have hbtarget (x : {x // x ∈ S}) :
      explicitSectionsComparison F (V x.1)
          (colimit.ι (F ⋙ sections (V x.1)) k (b x)) =
        (sheafify (Opens.grothendieckTopology X)
          (underlyingPresheafColimit F)).map (f x.1).op s := by
    rw [hbcolim]
    exact hc x.1
  let W : {x // x ∈ S} → Opens X := fun x => V x.1
  have heventual (x y : {x // x ∈ S}) :
      ∃ (m : I) (q : k ⟶ m),
        (F ⋙ sections (V x.1 ⊓ V y.1)).map q
            ((F.obj k).obj.map
              (homOfLE inf_le_left : (V x.1 ⊓ V y.1) ⟶ V x.1).op (b x)) =
          (F ⋙ sections (V x.1 ⊓ V y.1)).map q
            ((F.obj k).obj.map
              (homOfLE inf_le_right : (V x.1 ⊓ V y.1) ⟶ V y.1).op (b y)) := by
    apply ((colimit.isColimit (F ⋙ sections (W x ⊓ W y))).eq_iff' _ _).mp
    have hI : IsCompact ((W x ⊓ W y : Opens X) : Set X) :=
      (hVcompact x.1).inter_of_isOpen
        (hVcompact y.1) (V x.1).2 (V y.1).2
    apply explicitSectionsComparison_injective F (W x ⊓ W y) hI
    calc
      _ = (sheafify (Opens.grothendieckTopology X)
          (underlyingPresheafColimit F)).map
          (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op
          (explicitSectionsComparison F (W x)
            (colimit.ι (F ⋙ sections (W x)) k (b x))) :=
        explicitSectionsComparison_ι_naturality F
          (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x) k (b x)
      _ = (sheafify (Opens.grothendieckTopology X)
          (underlyingPresheafColimit F)).map
          (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op
          ((sheafify (Opens.grothendieckTopology X)
            (underlyingPresheafColimit F)).map (f x.1).op s) := by
              exact _root_.congr_arg
                ((sheafify (Opens.grothendieckTopology X)
                  (underlyingPresheafColimit F)).map
                    (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op)
                (hbtarget x)
      _ = (sheafify (Opens.grothendieckTopology X)
          (underlyingPresheafColimit F)).map
          (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op
          ((sheafify (Opens.grothendieckTopology X)
            (underlyingPresheafColimit F)).map (f y.1).op s) := by
              rw [← ConcreteCategory.comp_apply,
                ← ConcreteCategory.comp_apply,
                ← (sheafify (Opens.grothendieckTopology X)
                  (underlyingPresheafColimit F)).map_comp,
                ← (sheafify (Opens.grothendieckTopology X)
                  (underlyingPresheafColimit F)).map_comp]
              rfl
      _ = (sheafify (Opens.grothendieckTopology X)
          (underlyingPresheafColimit F)).map
          (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op
          (explicitSectionsComparison F (W y)
            (colimit.ι (F ⋙ sections (W y)) k (b y))) := by
              exact _root_.congr_arg
                ((sheafify (Opens.grothendieckTopology X)
                  (underlyingPresheafColimit F)).map
                    (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op)
                (hbtarget y).symm
      _ = _ := (explicitSectionsComparison_ι_naturality F
        (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y) k (b y)).symm
  let Pairs : Finset ({x // x ∈ S} × {x // x ∈ S}) := Finset.univ
  choose m q hq using fun z : {x // x ∈ S} × {x // x ∈ S} =>
    heventual z.1 z.2
  let O' : Finset I := insert k (Pairs.image m)
  have hkO' : k ∈ O' := by simp [O']
  have hmO' (z : {x // x ∈ S} × {x // x ∈ S}) : m z ∈ O' := by
    simp only [O', Finset.mem_insert, Finset.mem_image]
    exact Or.inr ⟨z, Finset.mem_univ z, rfl⟩
  let H' : Finset (Σ' (A B : I) (_ : A ∈ O') (_ : B ∈ O'), A ⟶ B) :=
    Pairs.attach.image fun z => ⟨k, m z.1, hkO', hmO' z.1, q z.1⟩
  let l : I := IsFiltered.sup O' H'
  let p' : k ⟶ l := IsFiltered.toSup O' H' hkO'
  let r (z : {x // x ∈ S} × {x // x ∈ S}) : m z ⟶ l :=
    IsFiltered.toSup O' H' (hmO' z)
  have hp' (z : {x // x ∈ S} × {x // x ∈ S}) :
      q z ≫ r z = p' := by
    apply IsFiltered.toSup_commutes O' H' hkO' (hmO' z)
    simp only [H', Finset.mem_image]
    exact ⟨⟨z, Finset.mem_univ z⟩,
      Finset.mem_attach Pairs ⟨z, Finset.mem_univ z⟩, rfl⟩
  let sf : ∀ x, ToType ((F.obj l).obj.obj (op (W x))) := fun x =>
    (F.map p').hom.app (op (W x)) (b x)
  have hcompat : ∀ x y,
      (F.obj l).obj.map
          (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op (sf x) =
        (F.obj l).obj.map
          (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op (sf y) := by
    intro x y
    let z : {x // x ∈ S} × {x // x ∈ S} := ⟨x, y⟩
    calc
      (F.obj l).obj.map
          (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op (sf x) =
        (F.map p').hom.app (op (W x ⊓ W y))
          ((F.obj k).obj.map
            (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op (b x)) := by
            simpa only [sf, ConcreteCategory.comp_apply] using
              (congr_hom ((F.map p').hom.naturality
                (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op) (b x)).symm
      _ = (F.map (r z)).hom.app (op (W x ⊓ W y))
          ((F.map (q z)).hom.app (op (W x ⊓ W y))
            ((F.obj k).obj.map
              (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op (b x))) := by
            rw [← hp' z, F.map_comp]
            change (((F.map (q z)).hom.app (op (W x ⊓ W y)) ≫
              (F.map (r z)).hom.app (op (W x ⊓ W y)))
                ((F.obj k).obj.map
                  (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op (b x))) = _
            rw [ConcreteCategory.comp_apply]
      _ = (F.map (r z)).hom.app (op (W x ⊓ W y))
          ((F.map (q z)).hom.app (op (W x ⊓ W y))
            ((F.obj k).obj.map
              (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op (b y))) := by
            exact _root_.congr_arg
              ((F.map (r z)).hom.app (op (W x ⊓ W y))) (hq z)
      _ = (F.map p').hom.app (op (W x ⊓ W y))
          ((F.obj k).obj.map
            (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op (b y)) := by
            rw [← hp' z, F.map_comp]
            change _ = (((F.map (q z)).hom.app (op (W x ⊓ W y)) ≫
              (F.map (r z)).hom.app (op (W x ⊓ W y)))
                ((F.obj k).obj.map
                  (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op (b y)))
            rw [ConcreteCategory.comp_apply]
      _ = (F.obj l).obj.map
          (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op (sf y) := by
            simpa only [sf, ConcreteCategory.comp_apply] using
              congr_hom ((F.map p').hom.naturality
                (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op) (b y)
  have hcoverOpen : U ≤ ⨆ x : {x // x ∈ S}, W x := by
    intro x hxU
    rw [Opens.mem_iSup]
    obtain ⟨y, hyS, hxy⟩ := Set.mem_iUnion₂.mp (hS hxU)
    exact ⟨⟨y, hyS⟩, hxy⟩
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (X := TopCat.of X) (F.obj l) W U
    (fun x => f x.1) hcoverOpen sf hcompat
  refine ⟨colimit.ι (F ⋙ sections U) l g, ?_⟩
  let aP := (presheafToSheaf (Opens.grothendieckTopology X)
    C).obj (underlyingPresheafColimit F)
  apply TopCat.Sheaf.eq_of_locally_eq'
    (X := TopCat.of X) aP W U (fun x => f x.1) hcoverOpen
  intro y
  calc
    (sheafify (Opens.grothendieckTopology X)
        (underlyingPresheafColimit F)).map (f y.1).op
        (explicitSectionsComparison F U
          (colimit.ι (F ⋙ sections U) l g)) =
      explicitSectionsComparison F (W y)
        (colimit.ι (F ⋙ sections (W y)) l
          ((F.obj l).obj.map (f y.1).op g)) := by
            exact (explicitSectionsComparison_ι_naturality F
              (f y.1) l g).symm
    _ = explicitSectionsComparison F (W y)
        (colimit.ι (F ⋙ sections (W y)) l (sf y)) := by rw [hg y]
    _ = explicitSectionsComparison F (W y)
        (colimit.ι (F ⋙ sections (W y)) k (b y)) := by
          apply _root_.congr_arg (explicitSectionsComparison F (W y))
          change colimit.ι (F ⋙ sections (W y)) l
              ((F ⋙ sections (W y)).map p' (b y)) = _
          rw [← ConcreteCategory.comp_apply]
          exact congr_hom (colimit.w (F ⋙ sections (W y)) p') (b y)
    _ = (sheafify (Opens.grothendieckTopology X)
        (underlyingPresheafColimit F)).map (f y.1).op s := hbtarget y

omit [UnivLE.{u, v}] in
include instCC instReflectsIsomorphisms in
/-- The direct comparison is an isomorphism on a compact open of a
prespectral, quasi-separated space. -/
theorem explicitSectionsComparison_isIso
    [PrespectralSpace X] [QuasiSeparatedSpace X]
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    IsIso (explicitSectionsComparison F U) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨explicitSectionsComparison_injective F U hU,
    explicitSectionsComparison_surjective F U hU⟩

omit [UnivLE.{u, v}] in
include instCC instReflectsIsomorphisms in
/-- The canonical colimit comparison for sections on a compact open is an
isomorphism. -/
theorem canonicalSectionsComparison_isIso
    [PrespectralSpace X] [QuasiSeparatedSpace X]
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    IsIso (colimit.post F (sections U)) := by
  rw [← transportedExplicitSectionsComparison_eq F U]
  unfold transportedExplicitSectionsComparison
  rw [ConcreteCategory.isIso_iff_bijective]
  have hmap := ((ConcreteCategory.isIso_iff_bijective
      ((sections U).map (explicitSheafColimitIso F).hom)).mp
        (by infer_instance))
  have hcomparison : Function.Bijective (explicitSectionsComparison F U) :=
    ⟨explicitSectionsComparison_injective F U hU,
      explicitSectionsComparison_surjective F U hU⟩
  constructor
  · intro x y h
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    exact hcomparison.1 (hmap.1 h)
  · intro z
    obtain ⟨y, hy⟩ := hmap.2 z
    obtain ⟨x, hx⟩ := hcomparison.2 y
    refine ⟨x, ?_⟩
    rw [ConcreteCategory.comp_apply, hx, hy]

omit [UnivLE.{u, v}] in
include instCC instReflectsIsomorphisms in
/-- Evaluation on a compact open preserves a filtered colimit of sheaves. -/
theorem preservesColimit_sections
    [PrespectralSpace X] [QuasiSeparatedSpace X]
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    PreservesColimit F (sections U) := by
  exact @preservesColimit_of_isIso_post
    _ _ _ _ (sections U) _ _ F _ _
    (canonicalSectionsComparison_isIso F U hU)

omit [UnivLE.{u, v}] in
include instCC instReflectsIsomorphisms in
/-- Global sections preserve a filtered colimit on a quasi-compact,
prespectral, quasi-separated space. -/
theorem preservesColimit_globalSections
    [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X] :
    PreservesColimit F (sections (⊤ : Opens X)) := by
  apply preservesColimit_sections F (⊤ : Opens X)
  simpa only [Opens.coe_top] using (isCompact_univ : IsCompact (Set.univ : Set X))

end SheafCohomology.CompactOpenSections
