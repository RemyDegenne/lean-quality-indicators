/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CompactFiniteTateNormSequence
public import ContinuousGroupCohomology.CompactExceptionalTateLimits
public import ContinuousGroupCohomology.RestrictedLevelCompact
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Connected

/-!
# Compact Tate norm limit sequence

The inverse limit of the actual finite coinvariants maps to total invariants
and then to the compact degree-zero Tate limit. All topologies are chosen by
`LevelCompact`; neither the coefficient ring nor the ambient representation
needs a topology. The full open-normal subgroup is named explicitly, since
`OpenNormalSubgroup` has no `Top` instance in the pinned mathlib.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}
variable (A : Rep.{u} R G) (L : LevelCompact A)

/-- The full group, explicitly packaged as an open normal subgroup. -/
@[expose] def fullOpenNormalSubgroup (G : ProfiniteGrp.{u}) : OpenNormalSubgroup G :=
  ⟨⊤, by change (⊤ : Subgroup G).Normal; infer_instance⟩

@[simp] theorem fullOpenNormalSubgroup_toOpenSubgroup (G : ProfiniteGrp.{u}) :
    (fullOpenNormalSubgroup G).toOpenSubgroup = ⊤ := rfl

theorem le_fullOpenNormalSubgroup (S : OpenNormalSubgroup G) :
    S ≤ fullOpenNormalSubgroup G := by
  change S.toOpenSubgroup ≤ (⊤ : OpenSubgroup G)
  exact le_top

/-- The relative norm at the full open-normal subgroup is the total norm. -/
theorem relativeNorm_fullOpenNormalSubgroup
    (S : OpenNormalSubgroup G) (h : S ≤ fullOpenNormalSubgroup G) :
    relativeNorm A (fullOpenNormalSubgroup G).toOpenSubgroup S.toOpenSubgroup h =
      relativeNorm A (⊤ : OpenSubgroup G) S.toOpenSubgroup le_top := by
  rfl

local instance : Nonempty (OpenNormalSubgroup G) := ⟨fullOpenNormalSubgroup G⟩
local instance : IsConnected (OpenNormalSubgroup G) :=
  IsCofiltered.isConnected (OpenNormalSubgroup G)
noncomputable local instance :
    HasLimitsOfShape (OpenNormalSubgroup G) CompHausAddCommGrp.{u} :=
  ⟨fun _ => inferInstance⟩

/-- The actual compact inverse limit of finite coinvariants. -/
abbrev compactFiniteCoinvariantsLimit : CompHausAddCommGrp.{u} :=
  lim.obj (compactFiniteCoinvariantsDiagram A L)

/-- The constant cone on total invariants, over the actual finite-row diagram. -/
@[expose] def compactTotalInvariantsCone : Cone (compactTotalInvariantsDiagram A L) :=
  { pt := group A L (⊤ : OpenSubgroup G)
    π := { app := fun _ => 𝟙 _ } }

@[expose] def compactTotalInvariantsCone_isLimit :
    IsLimit (compactTotalInvariantsCone A L) := by
  exact isLimitConstCone (OpenNormalSubgroup G) (group A L (⊤ : OpenSubgroup G))

/-- The constant limit is canonically isomorphic to total invariants. -/
@[expose] def compactTotalInvariantsLimitIso :
    limit (compactTotalInvariantsDiagram A L) ≅
      group A L (⊤ : OpenSubgroup G) :=
  (limit.isLimit (compactTotalInvariantsDiagram A L)).conePointUniqueUpToIso
    (compactTotalInvariantsCone_isLimit A L)

/-- Every projection from the constant invariant limit is the same iso map. -/
theorem compactTotalInvariantsLimitIso_hom (S : OpenNormalSubgroup G) :
    limit.π (compactTotalInvariantsDiagram A L) S =
      (compactTotalInvariantsLimitIso A L).hom := by
  have hh := (IsLimit.conePointUniqueUpToIso_hom_comp
    (limit.isLimit (compactTotalInvariantsDiagram A L))
    (compactTotalInvariantsCone_isLimit A L) S).symm
  simpa [compactTotalInvariantsLimitIso, compactTotalInvariantsCone] using hh

/-- Inclusion of the degree-`-1` Tate limit in the coinvariant limit. -/
@[expose] def compactTateLimitInclusion :
    compactNegativeOneTateLimit A L ⟶ compactFiniteCoinvariantsLimit A L :=
  lim.map (compactFiniteTateNegOneInclusion A L)

/-- The compatible finite norms, now valued in total invariants. -/
@[expose] def compactTateLimitNorm :
    compactFiniteCoinvariantsLimit A L ⟶ group A L (⊤ : OpenSubgroup G) :=
  lim.map (compactFiniteTateNorm A L) ≫
    (compactTotalInvariantsLimitIso A L).hom

/-- The compatible finite quotient projections from total invariants. -/
@[expose] def compactTateLimitProjection :
    group A L (⊤ : OpenSubgroup G) ⟶ compactZeroTateLimit A L :=
  (compactTotalInvariantsLimitIso A L).inv ≫
    lim.map (compactFiniteTateZeroProjection A L)

theorem compactTateLimitInclusion_π (S : OpenNormalSubgroup G) :
    compactTateLimitInclusion A L ≫
        limit.π (compactFiniteCoinvariantsDiagram A L) S =
      limit.π (compactFiniteNegativeOneDeflationDiagram A L) S ≫
        finiteTateNegOneι A L S := by
  exact limit.map_π (compactFiniteTateNegOneInclusion A L) S

theorem compactTateLimitNorm_π (S : OpenNormalSubgroup G) :
    compactTateLimitNorm A L =
      limit.π (compactFiniteCoinvariantsDiagram A L) S ≫
        normFromFiniteCoinvariants A L S := by
  have hp := limit.map_π (compactFiniteTateNorm A L) S
  change lim.map (compactFiniteTateNorm A L) ≫
      (compactTotalInvariantsLimitIso A L).hom =
    limit.π (compactFiniteCoinvariantsDiagram A L) S ≫
      normFromFiniteCoinvariants A L S
  simpa only [compactTotalInvariantsDiagram_obj,
    compactTotalInvariantsLimitIso_hom A L S, compactFiniteTateNorm_app] using hp

theorem compactTateLimitProjection_π (S : OpenNormalSubgroup G) :
    compactTateLimitProjection A L ≫
        limit.π (compactFiniteZeroDeflationDiagram A L) S =
      finiteTateZeroπ A L S := by
  have hp := limit.map_π (compactFiniteTateZeroProjection A L) S
  change (compactTotalInvariantsLimitIso A L).inv ≫
    (lim.map (compactFiniteTateZeroProjection A L) ≫
      limit.π (compactFiniteZeroDeflationDiagram A L) S) = finiteTateZeroπ A L S
  rw [hp]
  simp only [compactTotalInvariantsDiagram_obj,
    compactTotalInvariantsLimitIso_hom A L S, compactFiniteTateZeroProjection_app]
  exact Iso.inv_hom_id_assoc (compactTotalInvariantsLimitIso A L) _

/-- Exactness at the full coinvariant inverse limit. -/
theorem compactTateLimit_exact_left :
    Function.Exact (compactTateLimitInclusion A L)
      (compactTateLimitNorm A L) := by
  have he := CompHausAddCommGrp.limit_map_exact.{u,u}
    (compactFiniteNegativeOneDeflationDiagram A L)
    (compactFiniteCoinvariantsDiagram A L)
    (compactFiniteTateNegOneInclusion A L)
    (compactTotalInvariantsDiagram A L)
    (compactFiniteTateNorm A L)
    (fun S => finiteTateNorm_exact_left A L S)
  intro x
  constructor
  · intro hx
    apply (he x).mp
    have hy := congrArg (fun z => (compactTotalInvariantsLimitIso A L).inv z) hx
    change (compactTotalInvariantsLimitIso A L).inv
      ((compactTotalInvariantsLimitIso A L).hom (lim.map (compactFiniteTateNorm A L) x)) =
      (compactTotalInvariantsLimitIso A L).inv 0 at hy
    simpa only [Iso.hom_inv_id_apply, map_zero] using hy
  · intro hx
    have hy := (he x).mpr hx
    change (compactTotalInvariantsLimitIso A L).hom
      (lim.map (compactFiniteTateNorm A L) x) = 0
    rw [hy, map_zero]

/-- Exactness at total invariants after transporting the constant limit. -/
theorem compactTateLimit_exact_right :
    Function.Exact (compactTateLimitNorm A L)
      (compactTateLimitProjection A L) := by
  have he := CompHausAddCommGrp.limit_map_exact.{u,u}
    (compactFiniteCoinvariantsDiagram A L)
    (compactTotalInvariantsDiagram A L)
    (compactFiniteTateNorm A L)
    (compactFiniteZeroDeflationDiagram A L)
    (compactFiniteTateZeroProjection A L)
    (fun S => finiteTateNorm_exact_right A L S)
  intro x
  constructor
  · intro hx
    have hy : lim.map (compactFiniteTateZeroProjection A L)
        ((compactTotalInvariantsLimitIso A L).inv x) = 0 := hx
    obtain ⟨y, hy⟩ := (he _).mp hy
    exact ⟨y, by
      change (compactTotalInvariantsLimitIso A L).hom
        (lim.map (compactFiniteTateNorm A L) y) = x
      rw [hy]
      exact Iso.inv_hom_id_apply _ _⟩
  · rintro ⟨y, rfl⟩
    exact (he _).mpr ⟨y, by
      change lim.map (compactFiniteTateNorm A L) y =
        (compactTotalInvariantsLimitIso A L).inv
          ((compactTotalInvariantsLimitIso A L).hom
            (lim.map (compactFiniteTateNorm A L) y))
      exact (Iso.hom_inv_id_apply (compactTotalInvariantsLimitIso A L) _).symm⟩

private theorem compactLimit_element_ext
    (F : OpenNormalSubgroup G ⥤ CompHausAddCommGrp.{u})
    (x y : (limit F : CompHausAddCommGrp))
    (h : ∀ S, limit.π F S x = limit.π F S y) : x = y := by
  let cone : LimitCone F := ⟨CompHausAddCommGrp.limitCone F,
    CompHausAddCommGrp.limitConeIsLimit F⟩
  let iso := limit.isoLimitCone cone
  apply ((forget CompHausAddCommGrp).mapIso iso).toEquiv.injective
  apply Subtype.ext
  funext S
  have hx := ConcreteCategory.congr_hom (limit.isoLimitCone_hom_π cone S) x
  have hy := ConcreteCategory.congr_hom (limit.isoLimitCone_hom_π cone S) y
  exact hx.trans ((h S).trans hy.symm)

/-- The limit inclusion is injective although its transitions need not be onto. -/
theorem compactTateLimitInclusion_injective :
    Function.Injective (compactTateLimitInclusion A L) := by
  intro x y hxy
  apply compactLimit_element_ext (compactFiniteNegativeOneDeflationDiagram A L)
  intro S
  apply finiteTateNegOneι_injective A L S
  have hx := ConcreteCategory.congr_hom (compactTateLimitInclusion_π A L S) x
  have hy := ConcreteCategory.congr_hom (compactTateLimitInclusion_π A L S) y
  change limit.π (compactFiniteCoinvariantsDiagram A L) S
      (compactTateLimitInclusion A L x) = finiteTateNegOneι A L S
        (limit.π (compactFiniteNegativeOneDeflationDiagram A L) S x) at hx
  change limit.π (compactFiniteCoinvariantsDiagram A L) S
      (compactTateLimitInclusion A L y) = finiteTateNegOneι A L S
        (limit.π (compactFiniteNegativeOneDeflationDiagram A L) S y) at hy
  have hp := congrArg
    (fun c => limit.π (compactFiniteCoinvariantsDiagram A L) S c) hxy
  simpa only [compactFiniteCoinvariantsDiagram_obj] using hx.symm.trans (hp.trans hy)

/-- Surjectivity of the degree-zero limit projection, without assumptions on
coinvariant or kernel transitions. -/
theorem compactTateLimitProjection_surjective :
    Function.Surjective (compactTateLimitProjection A L) := by
  have hs := CompHausAddCommGrp.limit_map_surjective.{u,u}
    (compactTotalInvariantsDiagram A L)
    (compactFiniteZeroDeflationDiagram A L)
    (compactFiniteTateZeroProjection A L)
    (fun S => finiteTateZeroπ_surjective A L S)
  intro q
  obtain ⟨t, ht⟩ := hs q
  refine ⟨(compactTotalInvariantsLimitIso A L).hom t, ?_⟩
  change lim.map (compactFiniteTateZeroProjection A L)
    ((compactTotalInvariantsLimitIso A L).inv
      ((compactTotalInvariantsLimitIso A L).hom t)) = q
  rw [Iso.hom_inv_id_apply, ht]

/-- Every degree-zero stage projection is surjective via the finite quotient. -/
theorem compactZeroTateLimitπ_surjective (S : OpenNormalSubgroup G) :
    Function.Surjective (limit.π (compactFiniteZeroDeflationDiagram A L) S) := by
  intro z
  obtain ⟨y, rfl⟩ := finiteTateZeroπ_surjective A L S z
  refine ⟨compactTateLimitProjection A L y, ?_⟩
  exact ConcreteCategory.congr_hom (compactTateLimitProjection_π A L S) y

/-- The intersection of the ranges of the actual finite coinvariant norms. -/
@[expose] def compactUniversalNormSet : Set (group A L (⊤ : OpenSubgroup G)) :=
  {x | ∀ S : OpenNormalSubgroup G,
    x ∈ Set.range (normFromFiniteCoinvariants A L S)}

/-- A finite coinvariant representative identifies the finite norm range
with the range of the corresponding relative norm. -/
theorem mem_finiteNorm_range_iff_relativeNorm_range
    (S : OpenNormalSubgroup G) (x : group A L (⊤ : OpenSubgroup G)) :
    x ∈ Set.range (normFromFiniteCoinvariants A L S) ↔
      x ∈ LinearMap.range
        (relativeNorm A (⊤ : OpenSubgroup G) S.toOpenSubgroup le_top) := by
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    exact ⟨y, normFromFiniteCoinvariants_mk A L S y⟩
  · rintro ⟨y, hy⟩
    refine ⟨finiteCoinvariantsMk A L S y, ?_⟩
    rw [finiteCoinvariantsMk_apply, normFromFiniteCoinvariants_mk]
    exact hy

/-- The full-system intersection is the carrier of the published universal-norm
submodule at the explicit full open-normal subgroup. -/
theorem mem_compactUniversalNormSet_iff (x : group A L (⊤ : OpenSubgroup G)) :
    x ∈ compactUniversalNormSet A L ↔
      x ∈ universalNormSubmodule A (fullOpenNormalSubgroup G) := by
  let y : openSubgroupInvariants A (fullOpenNormalSubgroup G).toOpenSubgroup := x
  change (∀ S : OpenNormalSubgroup G,
      x ∈ Set.range (normFromFiniteCoinvariants A L S)) ↔
    y ∈ universalNormSubmodule A (fullOpenNormalSubgroup G)
  rw [mem_universalNormSubmodule_iff]
  constructor
  · intro hx S h
    have hs := (mem_finiteNorm_range_iff_relativeNorm_range A L S x).mp (hx S)
    change y ∈ LinearMap.range
      (relativeNorm A (⊤ : OpenSubgroup G) S.toOpenSubgroup le_top) at hs
    rw [relativeNorm_fullOpenNormalSubgroup A S h]
    exact hs
  · intro hx S
    apply (mem_finiteNorm_range_iff_relativeNorm_range A L S x).mpr
    have hy := hx S (le_fullOpenNormalSubgroup S)
    change x ∈ LinearMap.range
      (relativeNorm A (fullOpenNormalSubgroup G).toOpenSubgroup S.toOpenSubgroup
        (le_fullOpenNormalSubgroup S)) at hy
    rw [relativeNorm_fullOpenNormalSubgroup A S (le_fullOpenNormalSubgroup S)] at hy
    exact hy

/-- The projection kernel is exactly the full-system norm intersection. -/
theorem compactTateLimitProjection_eq_zero_iff
    (x : group A L (⊤ : OpenSubgroup G)) :
    compactTateLimitProjection A L x = 0 ↔
      x ∈ compactUniversalNormSet A L := by
  constructor
  · intro hx S
    apply (finiteTateNorm_exact_right A L S x).mp
    have hs := ConcreteCategory.congr_hom (compactTateLimitProjection_π A L S) x
    change limit.π (compactFiniteZeroDeflationDiagram A L) S
        (compactTateLimitProjection A L x) = finiteTateZeroπ A L S x at hs
    have hπ := congrArg
      (fun z => limit.π (compactFiniteZeroDeflationDiagram A L) S z) hx
    have hz : limit.π (compactFiniteZeroDeflationDiagram A L) S
        (0 : compactZeroTateLimit A L) = 0 := map_zero _
    have heq := hs.symm.trans (hπ.trans hz)
    change finiteTateZeroπ A L S x = 0 at heq
    exact heq
  · intro hx
    apply compactLimit_element_ext (compactFiniteZeroDeflationDiagram A L)
    intro S
    have hs := ConcreteCategory.congr_hom (compactTateLimitProjection_π A L S) x
    change limit.π (compactFiniteZeroDeflationDiagram A L) S
        (compactTateLimitProjection A L x) = finiteTateZeroπ A L S x at hs
    have hq := (finiteTateNorm_exact_right A L S x).mpr (hx S)
    have hz : limit.π (compactFiniteZeroDeflationDiagram A L) S
        (0 : compactZeroTateLimit A L) = 0 := map_zero _
    have heq := hs.trans hq
    rw [hz]
    exact heq

/-- The range of the limit norm is the full-system universal norm carrier. -/
theorem compactTateLimitNorm_range_eq_universalNormSet :
    Set.range (compactTateLimitNorm A L) = compactUniversalNormSet A L := by
  ext x
  exact (compactTateLimit_exact_right A L x).symm.trans
    (compactTateLimitProjection_eq_zero_iff A L x)

/-- The kernel is the carrier of the original universal-norm submodule. -/
theorem compactTateLimitProjection_eq_zero_iff_universalNorm
    (x : group A L (⊤ : OpenSubgroup G)) :
    compactTateLimitProjection A L x = 0 ↔
      x ∈ universalNormSubmodule A (fullOpenNormalSubgroup G) :=
  (compactTateLimitProjection_eq_zero_iff A L x).trans
    (mem_compactUniversalNormSet_iff A L x)

/-- The norm-limit range is the carrier of the universal-norm submodule. -/
theorem compactTateLimitNorm_range_eq_universalNormSubmodule :
    Set.range (compactTateLimitNorm A L) =
      {x : group A L (⊤ : OpenSubgroup G) |
        x ∈ universalNormSubmodule A (fullOpenNormalSubgroup G)} := by
  ext x
  rw [compactTateLimitNorm_range_eq_universalNormSet]
  exact mem_compactUniversalNormSet_iff A L x

/-- The published universal-norm submodule, closed in precisely the selected
`L.topology ⊤`, as a closed additive subgroup of total invariants. -/
@[expose] def compactUniversalNormClosedSubgroup :
    ClosedAddSubgroup (group A L (⊤ : OpenSubgroup G)) where
  toAddSubgroup := (universalNormSubmodule A (fullOpenNormalSubgroup G)).toAddSubgroup
  isClosed' := by
    change @IsClosed
      (openSubgroupInvariants A (fullOpenNormalSubgroup G).toOpenSubgroup)
      (L.topology (fullOpenNormalSubgroup G).toOpenSubgroup)
      (universalNormSubmodule A (fullOpenNormalSubgroup G) : Set _)
    exact isClosed_universalNormSubmodule A L (fullOpenNormalSubgroup G)

/-- The closed universal norms are the actual kernel of the limit projection. -/
theorem compactUniversalNormClosedSubgroup_eq_ker :
    (compactUniversalNormClosedSubgroup A L).toAddSubgroup =
      (compactTateLimitProjection A L).hom.toAddMonoidHom.ker := by
  ext x
  change x ∈ universalNormSubmodule A (fullOpenNormalSubgroup G) ↔
    compactTateLimitProjection A L x = 0
  exact (mem_compactUniversalNormSet_iff A L x).symm.trans
    (compactTateLimitProjection_eq_zero_iff A L x).symm

/-- The descended additive equivalence; continuity is proved separately below. -/
@[expose] def compactTateUniversalNormQuotientEquiv :
    (group A L (⊤ : OpenSubgroup G) ⧸
      (compactUniversalNormClosedSubgroup A L).toAddSubgroup) ≃+
        compactZeroTateLimit A L :=
  QuotientAddGroup.liftEquiv
    (compactUniversalNormClosedSubgroup A L).toAddSubgroup
    (φ := (compactTateLimitProjection A L).hom.toAddMonoidHom)
    (compactTateLimitProjection_surjective A L)
    (compactUniversalNormClosedSubgroup_eq_ker A L)

/-- The descended map agrees with the actual limit projection on representatives. -/
theorem compactTateUniversalNormQuotientEquiv_mk
    (x : group A L (⊤ : OpenSubgroup G)) :
    compactTateUniversalNormQuotientEquiv A L (QuotientAddGroup.mk x) =
      compactTateLimitProjection A L x := by
  exact QuotientAddGroup.liftEquiv_mk
    (compactUniversalNormClosedSubgroup A L).toAddSubgroup
    (compactTateLimitProjection_surjective A L)
    (compactUniversalNormClosedSubgroup_eq_ker A L) x

/-- The actual descended additive equivalence is continuous for the compact
quotient topology, rather than merely a bijection of underlying groups. -/
theorem compactTateUniversalNormQuotientEquiv_continuous :
    Continuous (compactTateUniversalNormQuotientEquiv A L :
      (group A L (⊤ : OpenSubgroup G) ⧸
        (compactUniversalNormClosedSubgroup A L).toAddSubgroup) →
      compactZeroTateLimit A L) := by
  apply continuous_coinduced_dom.2
  change Continuous (fun x : group A L (⊤ : OpenSubgroup G) =>
    compactTateUniversalNormQuotientEquiv A L (QuotientAddGroup.mk x))
  have hcont := (compactTateLimitProjection A L).hom.continuous
  change Continuous (fun x : group A L (⊤ : OpenSubgroup G) =>
    compactTateLimitProjection A L x) at hcont
  simpa only [compactTateUniversalNormQuotientEquiv_mk] using hcont

/-- The compact quotient by closed universal norms is isomorphic, as a
compact Hausdorff additive group, to the actual degree-zero Tate limit. -/
@[expose] def compactTateUniversalNormQuotientIso :
    CompHausAddCommGrp.quotient (group A L (⊤ : OpenSubgroup G))
      (compactUniversalNormClosedSubgroup A L) ≅ compactZeroTateLimit A L := by
  let equiv := compactTateUniversalNormQuotientEquiv A L
  let homeo := Continuous.homeoOfEquivCompactToT2 (f := equiv.toEquiv)
    (compactTateUniversalNormQuotientEquiv_continuous A L)
  refine
    { hom := ConcreteCategory.ofHom
        { toAddMonoidHom := equiv.toAddMonoidHom
          continuous_toFun := homeo.continuous }
      inv := ConcreteCategory.ofHom
        { toAddMonoidHom := equiv.symm.toAddMonoidHom
          continuous_toFun := homeo.symm.continuous }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply CompHausAddCommGrp.hom_ext
    ext x
    exact equiv.symm_apply_apply x
  · apply CompHausAddCommGrp.hom_ext
    ext x
    exact equiv.apply_symm_apply x

/-- The quotient iso descends the original projection, on every representative. -/
theorem compactTateUniversalNormQuotientIso_mk
    (x : group A L (⊤ : OpenSubgroup G)) :
    (compactTateUniversalNormQuotientIso A L).hom (QuotientAddGroup.mk x) =
      compactTateLimitProjection A L x := by
  change compactTateUniversalNormQuotientEquiv A L (QuotientAddGroup.mk x) =
    compactTateLimitProjection A L x
  exact compactTateUniversalNormQuotientEquiv_mk A L x

end ContinuousGroupCohomology.LevelCompact
