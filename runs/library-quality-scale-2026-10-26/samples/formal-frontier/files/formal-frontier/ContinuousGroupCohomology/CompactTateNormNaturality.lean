/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CompactTateNormLimitSequence
public import ContinuousGroupCohomology.CompactExceptionalTateLimitFunctoriality
public import ContinuousGroupCohomology.RestrictedLevelCompactFunctoriality

/-!
# Coefficient naturality of the compact Tate norm row

Level-compact coefficient morphisms act on the actual compact finite-coinvariant
diagram and its inverse limit. The resulting maps commute with the three arrows
of the full compact Tate norm row. In particular the quotient by closed universal
norms carries the independently descended coefficient action, and the existing
quotient-to-degree-zero-limit isomorphism is natural for that action.

The topology at each level is the chosen `LevelCompact` topology. Neither the
coefficient ring nor the ambient representation carries a topology.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology.LevelCompactRep

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}

noncomputable local instance :
    HasLimitsOfShape (OpenNormalSubgroup G) CompHausAddCommGrp.{u} :=
  ⟨fun _ => inferInstance⟩

/-- Coefficient functoriality of the actual finite-coinvariant deflation diagram. -/
@[expose] def compactFiniteCoinvariantsDiagramFunctor :
    LevelCompactRep.{u, u, u} R G ⥤
      (OpenNormalSubgroup G ⥤ CompHausAddCommGrp.{u}) where
  obj A := LevelCompact.compactFiniteCoinvariantsDiagram A.rep A.levelCompact
  map {A B} f :=
    { app := fun S => finiteCoinvariantsMap f S
      naturality := by
        intro S T hST
        let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
          Fintype.ofFinite _
        exact (finiteCoinvariantsMap_deflation f S T (leOfHom hST)).symm }
  map_id A := by
    apply NatTrans.ext
    funext S
    exact finiteCoinvariantsMap_id A S
  map_comp f g := by
    apply NatTrans.ext
    funext S
    exact finiteCoinvariantsMap_comp f g S

@[simp] theorem compactFiniteCoinvariantsDiagramFunctor_obj
    (A : LevelCompactRep.{u, u, u} R G) :
    compactFiniteCoinvariantsDiagramFunctor.obj A =
      LevelCompact.compactFiniteCoinvariantsDiagram A.rep A.levelCompact := rfl

@[simp] theorem compactFiniteCoinvariantsDiagramFunctor_map_app
    {A B : LevelCompactRep.{u, u, u} R G} (f : A ⟶ B)
    (S : OpenNormalSubgroup G) :
    (compactFiniteCoinvariantsDiagramFunctor.map f).app S =
      finiteCoinvariantsMap f S := rfl

/-- Continuous coefficient maps on the actual compact finite-coinvariant limit. -/
@[expose] def compactFiniteCoinvariantsLimitFunctor :
    LevelCompactRep.{u, u, u} R G ⥤ CompHausAddCommGrp.{u} :=
  compactFiniteCoinvariantsDiagramFunctor ⋙ lim

@[simp] theorem compactFiniteCoinvariantsLimitFunctor_obj
    (A : LevelCompactRep.{u, u, u} R G) :
    compactFiniteCoinvariantsLimitFunctor.obj A =
      LevelCompact.compactFiniteCoinvariantsLimit A.rep A.levelCompact := rfl

/-- The stage component of the map on the actual coinvariant inverse limit. -/
@[reassoc] theorem compactFiniteCoinvariantsLimitFunctor_map_π
    {A B : LevelCompactRep.{u, u, u} R G} (f : A ⟶ B)
    (S : OpenNormalSubgroup G) :
    compactFiniteCoinvariantsLimitFunctor.map f ≫
        limit.π (LevelCompact.compactFiniteCoinvariantsDiagram B.rep B.levelCompact) S =
      limit.π (LevelCompact.compactFiniteCoinvariantsDiagram A.rep A.levelCompact) S ≫
        finiteCoinvariantsMap f S := by
  exact limit.map_π (compactFiniteCoinvariantsDiagramFunctor.map f) S

/-- Continuous coefficient maps on the actual compact total-invariants group. -/
@[expose] def compactTotalInvariantsFunctor :
    LevelCompactRep.{u, u, u} R G ⥤ CompHausAddCommGrp.{u} where
  obj A := LevelCompact.group A.rep A.levelCompact (⊤ : OpenSubgroup G)
  map f := groupMap f (⊤ : OpenSubgroup G)
  map_id A := groupMap_id A (⊤ : OpenSubgroup G)
  map_comp f g := groupMap_comp f g (⊤ : OpenSubgroup G)

/-- Naturality of the kernel inclusion in the actual compact norm row. -/
@[reassoc] theorem compactTateLimitInclusion_naturality
    {A B : LevelCompactRep.{u, u, u} R G} (f : A ⟶ B) :
    compactNegativeOneTateLimitFunctor.map f ≫
        LevelCompact.compactTateLimitInclusion B.rep B.levelCompact =
      LevelCompact.compactTateLimitInclusion A.rep A.levelCompact ≫
        compactFiniteCoinvariantsLimitFunctor.map f := by
  have hfinite : compactFiniteNegativeOneDeflationDiagramFunctor.map f ≫
        LevelCompact.compactFiniteTateNegOneInclusion B.rep B.levelCompact =
      LevelCompact.compactFiniteTateNegOneInclusion A.rep A.levelCompact ≫
        compactFiniteCoinvariantsDiagramFunctor.map f := by
    apply NatTrans.ext
    funext S
    apply CompHausAddCommGrp.hom_ext
    ext x
    exact finiteTateNegOneι_finiteTateNegOneMap_apply f S x
  change lim.map (compactFiniteNegativeOneDeflationDiagramFunctor.map f) ≫
      lim.map (LevelCompact.compactFiniteTateNegOneInclusion B.rep B.levelCompact) =
    lim.map (LevelCompact.compactFiniteTateNegOneInclusion A.rep A.levelCompact) ≫
      lim.map (compactFiniteCoinvariantsDiagramFunctor.map f)
  exact (Functor.map_comp lim
      (compactFiniteNegativeOneDeflationDiagramFunctor.map f)
      (LevelCompact.compactFiniteTateNegOneInclusion B.rep B.levelCompact)).symm.trans
    ((congrArg (fun η => lim.map η) hfinite).trans
      (Functor.map_comp lim
        (LevelCompact.compactFiniteTateNegOneInclusion A.rep A.levelCompact)
        (compactFiniteCoinvariantsDiagramFunctor.map f)))

/-- Naturality of the norm from the actual compact finite-coinvariant limit. -/
@[reassoc] theorem compactTateLimitNorm_naturality
    {A B : LevelCompactRep.{u, u, u} R G} (f : A ⟶ B) :
    compactFiniteCoinvariantsLimitFunctor.map f ≫
        LevelCompact.compactTateLimitNorm B.rep B.levelCompact =
      LevelCompact.compactTateLimitNorm A.rep A.levelCompact ≫
        groupMap f (⊤ : OpenSubgroup G) := by
  let S := LevelCompact.fullOpenNormalSubgroup G
  apply CompHausAddCommGrp.hom_ext
  ext x
  change LevelCompact.compactTateLimitNorm B.rep B.levelCompact
      (compactFiniteCoinvariantsLimitFunctor.map f x) =
    groupMap f (⊤ : OpenSubgroup G)
      (LevelCompact.compactTateLimitNorm A.rep A.levelCompact x)
  have hcoinvariant := CategoryTheory.congr_fun
    (compactFiniteCoinvariantsLimitFunctor_map_π f S) x
  have hnorm := CategoryTheory.congr_fun
    (LevelCompact.compactTateLimitNorm_π A.rep A.levelCompact S) x
  calc
    _ = LevelCompact.normFromFiniteCoinvariants B.rep B.levelCompact S
        ((limit.π (LevelCompact.compactFiniteCoinvariantsDiagram
          B.rep B.levelCompact) S)
          (compactFiniteCoinvariantsLimitFunctor.map f x)) :=
            CategoryTheory.congr_fun
              (LevelCompact.compactTateLimitNorm_π B.rep B.levelCompact S) _
    _ = LevelCompact.normFromFiniteCoinvariants B.rep B.levelCompact S
        (finiteCoinvariantsMap f S
          ((limit.π (LevelCompact.compactFiniteCoinvariantsDiagram
            A.rep A.levelCompact) S) x)) := congrArg _ hcoinvariant
    _ = groupMap f (⊤ : OpenSubgroup G)
        (LevelCompact.normFromFiniteCoinvariants A.rep A.levelCompact S
          ((limit.π (LevelCompact.compactFiniteCoinvariantsDiagram
            A.rep A.levelCompact) S) x)) :=
          CategoryTheory.congr_fun (normFromFiniteCoinvariants_naturality_hom f S) _
    _ = _ := congrArg _ hnorm.symm

/-- Naturality of the projection to the actual compact degree-zero Tate limit. -/
@[reassoc] theorem compactTateLimitProjection_naturality
    {A B : LevelCompactRep.{u, u, u} R G} (f : A ⟶ B) :
    groupMap f (⊤ : OpenSubgroup G) ≫
        LevelCompact.compactTateLimitProjection B.rep B.levelCompact =
      LevelCompact.compactTateLimitProjection A.rep A.levelCompact ≫
        compactZeroTateLimitFunctor.map f := by
  apply limit.hom_ext
  intro S
  apply CompHausAddCommGrp.hom_ext
  ext x
  change (limit.π (LevelCompact.compactFiniteZeroDeflationDiagram
      B.rep B.levelCompact) S)
      (LevelCompact.compactTateLimitProjection B.rep B.levelCompact
        (groupMap f (⊤ : OpenSubgroup G) x)) =
    (limit.π (LevelCompact.compactFiniteZeroDeflationDiagram
      B.rep B.levelCompact) S)
      (compactZeroTateLimitFunctor.map f
        (LevelCompact.compactTateLimitProjection A.rep A.levelCompact x))
  have hzero := CategoryTheory.congr_fun
    (compactZeroTateLimitFunctor_map_π f S)
    (LevelCompact.compactTateLimitProjection A.rep A.levelCompact x)
  have hleft := CategoryTheory.congr_fun
    (LevelCompact.compactTateLimitProjection_π B.rep B.levelCompact S)
    (groupMap f (⊤ : OpenSubgroup G) x)
  have hright := CategoryTheory.congr_fun
    (LevelCompact.compactTateLimitProjection_π A.rep A.levelCompact S) x
  have hfinite := finiteTateZeroMap_finiteTateZeroπ_apply f S x
  change (limit.π (LevelCompact.compactFiniteZeroDeflationDiagram
      B.rep B.levelCompact) S)
      (LevelCompact.compactTateLimitProjection B.rep B.levelCompact
        (groupMap f (⊤ : OpenSubgroup G) x)) =
    LevelCompact.finiteTateZeroπ B.rep B.levelCompact S
      (groupMap f (⊤ : OpenSubgroup G) x) at hleft
  change (limit.π (LevelCompact.compactFiniteZeroDeflationDiagram
      A.rep A.levelCompact) S)
      (LevelCompact.compactTateLimitProjection A.rep A.levelCompact x) =
    LevelCompact.finiteTateZeroπ A.rep A.levelCompact S x at hright
  change (limit.π (LevelCompact.compactFiniteZeroDeflationDiagram
      B.rep B.levelCompact) S)
      (compactZeroTateLimitFunctor.map f
        (LevelCompact.compactTateLimitProjection A.rep A.levelCompact x)) =
    finiteTateZeroMap f S
      ((limit.π (LevelCompact.compactFiniteZeroDeflationDiagram
        A.rep A.levelCompact) S)
        (LevelCompact.compactTateLimitProjection A.rep A.levelCompact x)) at hzero
  exact hleft.trans (hfinite.symm.trans ((congrArg _ hright.symm).trans hzero.symm))

/-- The full row's inclusion, as a natural transformation. -/
@[expose] def compactTateLimitInclusionNat :
    compactNegativeOneTateLimitFunctor (R := R) (G := G) ⟶
      compactFiniteCoinvariantsLimitFunctor where
  app A := LevelCompact.compactTateLimitInclusion A.rep A.levelCompact
  naturality {_ _} f := compactTateLimitInclusion_naturality f

/-- The full row's norm, as a natural transformation. -/
@[expose] def compactTateLimitNormNat :
    compactFiniteCoinvariantsLimitFunctor (R := R) (G := G) ⟶
      compactTotalInvariantsFunctor where
  app A := LevelCompact.compactTateLimitNorm A.rep A.levelCompact
  naturality {_ _} f := compactTateLimitNorm_naturality f

/-- The full row's projection, as a natural transformation. -/
@[expose] def compactTateLimitProjectionNat :
    compactTotalInvariantsFunctor (R := R) (G := G) ⟶
      compactZeroTateLimitFunctor where
  app A := LevelCompact.compactTateLimitProjection A.rep A.levelCompact
  naturality {_ _} f := compactTateLimitProjection_naturality f

/-- Coefficient maps preserve the closed universal-norm subgroup at the full
open-normal level, without a supplementary preservation hypothesis. -/
theorem groupMap_mem_compactUniversalNormClosedSubgroup
    {A B : LevelCompactRep.{u, u, u} R G} (f : A ⟶ B)
    {x : LevelCompact.group A.rep A.levelCompact (⊤ : OpenSubgroup G)}
    (hx : x ∈ LevelCompact.compactUniversalNormClosedSubgroup A.rep A.levelCompact) :
    groupMap f (⊤ : OpenSubgroup G) x ∈
      LevelCompact.compactUniversalNormClosedSubgroup B.rep B.levelCompact := by
  change x ∈ LevelCompact.universalNormSubmodule A.rep
    (LevelCompact.fullOpenNormalSubgroup G) at hx
  change mapInvariants f (⊤ : OpenSubgroup G) x ∈
    LevelCompact.universalNormSubmodule B.rep
      (LevelCompact.fullOpenNormalSubgroup G)
  exact RestrictedLevelCompactRep.mapInvariants_mem_universalNorm f
    (LevelCompact.fullOpenNormalSubgroup G) hx

/-- The independently descended continuous coefficient map on the actual
compact quotient by closed universal norms. -/
@[expose] def compactUniversalNormQuotientMap
    {A B : LevelCompactRep.{u, u, u} R G} (f : A ⟶ B) :
    CompHausAddCommGrp.quotient
        (LevelCompact.group A.rep A.levelCompact (⊤ : OpenSubgroup G))
        (LevelCompact.compactUniversalNormClosedSubgroup A.rep A.levelCompact) ⟶
      CompHausAddCommGrp.quotient
        (LevelCompact.group B.rep B.levelCompact (⊤ : OpenSubgroup G))
        (LevelCompact.compactUniversalNormClosedSubgroup B.rep B.levelCompact) := by
  let φ : LevelCompact.group A.rep A.levelCompact (⊤ : OpenSubgroup G) →+
      CompHausAddCommGrp.quotient
        (LevelCompact.group B.rep B.levelCompact (⊤ : OpenSubgroup G))
        (LevelCompact.compactUniversalNormClosedSubgroup B.rep B.levelCompact) :=
    (QuotientAddGroup.mk' (LevelCompact.compactUniversalNormClosedSubgroup
      B.rep B.levelCompact).toAddSubgroup).comp
      (groupMap f (⊤ : OpenSubgroup G)).hom.toAddMonoidHom
  have hφ : (LevelCompact.compactUniversalNormClosedSubgroup
      A.rep A.levelCompact).toAddSubgroup ≤ φ.ker := by
    intro x hx
    change QuotientAddGroup.mk' _ (groupMap f (⊤ : OpenSubgroup G) x) = 0
    rw [← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk']
    exact groupMap_mem_compactUniversalNormClosedSubgroup f hx
  apply ConcreteCategory.ofHom
  refine
    { toAddMonoidHom := QuotientAddGroup.lift
        (LevelCompact.compactUniversalNormClosedSubgroup A.rep A.levelCompact).toAddSubgroup
        φ hφ
      continuous_toFun := ?_ }
  apply continuous_coinduced_dom.2
  exact continuous_quotient_mk'.comp (groupMap f (⊤ : OpenSubgroup G)).hom.continuous

/-- The descended coefficient action on quotient representatives. -/
@[simp] theorem compactUniversalNormQuotientMap_mk
    {A B : LevelCompactRep.{u, u, u} R G} (f : A ⟶ B)
    (x : LevelCompact.group A.rep A.levelCompact (⊤ : OpenSubgroup G)) :
    compactUniversalNormQuotientMap f (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (groupMap f (⊤ : OpenSubgroup G) x) := by
  rfl

@[simp] theorem compactUniversalNormQuotientMap_id
    (A : LevelCompactRep.{u, u, u} R G) :
    compactUniversalNormQuotientMap (𝟙 A) = 𝟙 _ := by
  apply CompHausAddCommGrp.hom_ext
  ext x
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
    change compactUniversalNormQuotientMap (𝟙 A) (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk x
    rw [compactUniversalNormQuotientMap_mk, groupMap_id]
    rfl

@[reassoc] theorem compactUniversalNormQuotientMap_comp
    {A B C : LevelCompactRep.{u, u, u} R G} (f : A ⟶ B) (g : B ⟶ C) :
    compactUniversalNormQuotientMap (f ≫ g) =
      compactUniversalNormQuotientMap f ≫ compactUniversalNormQuotientMap g := by
  apply CompHausAddCommGrp.hom_ext
  ext x
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
    change compactUniversalNormQuotientMap (f ≫ g) (QuotientAddGroup.mk x) =
      compactUniversalNormQuotientMap g
        (compactUniversalNormQuotientMap f (QuotientAddGroup.mk x))
    rw [compactUniversalNormQuotientMap_mk, compactUniversalNormQuotientMap_mk,
      compactUniversalNormQuotientMap_mk, groupMap_comp]
    rfl

/-- The actual quotient by closed universal norms is functorial in coefficients. -/
@[expose] def compactUniversalNormQuotientFunctor :
    LevelCompactRep.{u, u, u} R G ⥤ CompHausAddCommGrp.{u} where
  obj A := CompHausAddCommGrp.quotient
    (LevelCompact.group A.rep A.levelCompact (⊤ : OpenSubgroup G))
    (LevelCompact.compactUniversalNormClosedSubgroup A.rep A.levelCompact)
  map f := compactUniversalNormQuotientMap f
  map_id A := compactUniversalNormQuotientMap_id A
  map_comp f g := compactUniversalNormQuotientMap_comp f g

/-- The universal-norm quotient identification respects the
independently descended coefficient action. -/
@[reassoc] theorem compactTateUniversalNormQuotientIso_naturality
    {A B : LevelCompactRep.{u, u, u} R G} (f : A ⟶ B) :
    compactUniversalNormQuotientMap f ≫
        (LevelCompact.compactTateUniversalNormQuotientIso B.rep B.levelCompact).hom =
      (LevelCompact.compactTateUniversalNormQuotientIso A.rep A.levelCompact).hom ≫
        compactZeroTateLimitFunctor.map f := by
  apply CompHausAddCommGrp.hom_ext
  ext x
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
    change (LevelCompact.compactTateUniversalNormQuotientIso B.rep B.levelCompact).hom
        (compactUniversalNormQuotientMap f (QuotientAddGroup.mk x)) =
      compactZeroTateLimitFunctor.map f
        ((LevelCompact.compactTateUniversalNormQuotientIso A.rep A.levelCompact).hom
          (QuotientAddGroup.mk x))
    rw [compactUniversalNormQuotientMap_mk,
      LevelCompact.compactTateUniversalNormQuotientIso_mk,
      LevelCompact.compactTateUniversalNormQuotientIso_mk]
    exact CategoryTheory.congr_fun (compactTateLimitProjection_naturality f) x

/-- The objectwise quotient isomorphisms form a natural isomorphism
to the compact degree-zero Tate limit functor. -/
@[expose] def compactTateUniversalNormQuotientNatIso :
    compactUniversalNormQuotientFunctor (R := R) (G := G) ≅
      compactZeroTateLimitFunctor :=
  NatIso.ofComponents
    (fun A => LevelCompact.compactTateUniversalNormQuotientIso A.rep A.levelCompact)
    (fun f => compactTateUniversalNormQuotientIso_naturality f)

@[simp] theorem compactTateUniversalNormQuotientNatIso_hom_app
    (A : LevelCompactRep.{u, u, u} R G) :
    (compactTateUniversalNormQuotientNatIso.hom.app A) =
      (LevelCompact.compactTateUniversalNormQuotientIso A.rep A.levelCompact).hom := rfl

/-- The natural isomorphism is the original limit projection on representatives. -/
@[simp] theorem compactTateUniversalNormQuotientNatIso_hom_app_mk
    (A : LevelCompactRep.{u, u, u} R G)
    (x : LevelCompact.group A.rep A.levelCompact (⊤ : OpenSubgroup G)) :
    (compactTateUniversalNormQuotientNatIso.hom.app A) (QuotientAddGroup.mk x) =
      LevelCompact.compactTateLimitProjection A.rep A.levelCompact x := by
  rw [compactTateUniversalNormQuotientNatIso_hom_app]
  exact LevelCompact.compactTateUniversalNormQuotientIso_mk A.rep A.levelCompact x

end ContinuousGroupCohomology.LevelCompactRep
