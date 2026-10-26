/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CompactFiniteHomology
public import ContinuousGroupCohomology.FiniteCoinvariants
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Compact topologies on negative finite Tate stages

This file equips the finite inhomogeneous bar chains of a finite group acting
continuously on a compact Hausdorff additive commutative group with their
finite-product topologies.  The bar differentials are continuous, so positive
group homology, and hence finite Tate cohomology below degree `-1`, has an
honest compact Hausdorff topology.

Continuity of finite deflation between different open-normal levels, inverse
limits, cup products and exactness are separate later layers.

## References

The compact construction uses this library's `CompactFiniteHomology` and
`FiniteCoinvariants` finite-bar and invariant-coefficient approach. The
algebraic Tate-to-homology comparison is
`Mathlib.RepresentationTheory.Homological.TateCohomology.Basic`, by Yunzhou Xie
and Yaël Dillies. The original compact finite-bar and negative-Tate development
is credited in `docs/attribution.md`.
-/

public section

set_option warningAsError true

open CategoryTheory Topology

namespace CompHausAddCommGrp

universe u

/-- Multiplication by a sign is continuous without any topology on the scalar
ring. -/
lemma continuous_negOnePow_smul
    {R X : Type u} [Ring R] [AddCommGroup X] [Module R X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] (n : ℕ) :
    Continuous (fun x : X ↦ (-1 : R) ^ n • x) := by
  induction n with
  | zero =>
      have h : (fun x : X ↦ (-1 : R) ^ 0 • x) = id := by
        funext x
        simp
      rw [h]
      exact continuous_id
  | succ n ih =>
      have h : (fun x : X ↦ (-1 : R) ^ (n + 1) • x) =
          (fun x : X ↦ -x) ∘ (fun x : X ↦ (-1 : R) ^ n • x) := by
        funext x
        simp [pow_succ]
      rw [h]
      exact continuous_neg.comp ih

namespace FiniteBar

variable {R H : Type u} [CommRing R] [Group H] [Fintype H]
variable (B : Rep.{u} R H)
variable [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable [IsTopologicalAddGroup B]
variable (hρ : ∀ h, Continuous (B.ρ h))

/-- Finite inhomogeneous chains with the finite-product topology induced by
the compact Hausdorff topology on the coefficient group. -/
noncomputable abbrev chains (n : ℕ) : CompHausAddCommGrp.{u} :=
  finiteFinsupp (of B) (Fin n → H)

omit [Fintype H] [CompactSpace B] [T2Space B] in
private lemma differential_single_continuous
    (hρ : ∀ h, Continuous (B.ρ h)) (n : ℕ)
    (g : Fin (n + 1) → H) (y : Fin n → H) :
    Continuous (fun a : B ↦
      (groupHomology.inhomogeneousChains.d B n (Finsupp.single g a)) y) := by
  classical
  have hfirst : Continuous (fun a : B ↦
      (Finsupp.single (fun i ↦ g i.succ) (B.ρ (g 0)⁻¹ a)) y) := by
    by_cases h : (fun i ↦ g i.succ) = y
    · simpa [Finsupp.single_apply, h] using hρ (g 0)⁻¹
    · simpa [Finsupp.single_apply, h] using
        (continuous_const : Continuous (fun _ : B ↦ (0 : B)))
  have hterm (j : Fin (n + 1)) :
      Continuous (fun a : B ↦
        ((-1 : R) ^ ((j : ℕ) + 1) •
          Finsupp.single (Fin.contractNth j (· * ·) g) a) y) := by
    by_cases h : Fin.contractNth j (· * ·) g = y
    · simpa [Finsupp.single_apply, h] using
        (continuous_negOnePow_smul ((j : ℕ) + 1) :
          Continuous (fun a : B ↦ (-1 : R) ^ ((j : ℕ) + 1) • a))
    · simpa [Finsupp.single_apply, h] using
        (continuous_const : Continuous (fun _ : B ↦ (0 : B)))
  have hsum : Continuous (fun a : B ↦
      ∑ j : Fin (n + 1),
        ((-1 : R) ^ ((j : ℕ) + 1) •
          Finsupp.single (Fin.contractNth j (· * ·) g) a) y) :=
    continuous_finsetSum Finset.univ fun j _ ↦ hterm j
  convert hfirst.add hsum using 1
  funext a
  simpa using congrArg (· y)
    (groupHomology.inhomogeneousChains.d_single n g a)

/-- The inhomogeneous bar differential as a continuous additive homomorphism
between compact finite products. -/
noncomputable def differential (n : ℕ) : chains B (n + 1) ⟶ chains B n :=
  finiteFinsuppMap _ _ _ _
    (groupHomology.inhomogeneousChains.d B n).hom.toAddMonoidHom
    (differential_single_continuous B hρ n)

@[simp]
lemma differential_apply (n : ℕ) (x : chains B (n + 1)) :
    differential B hρ n x = groupHomology.inhomogeneousChains.d B n x :=
  by rfl

/-- The compact Hausdorff homology of the finite inhomogeneous bar complex in
degree `n + 1`. -/
@[expose] noncomputable def positiveHomology (n : ℕ) : CompHausAddCommGrp.{u} :=
  CompHausAddCommGrp.homology
    (differential B hρ (n + 1)) (differential B hρ n)
    (fun x ↦ by
      change groupHomology.inhomogeneousChains.d B n
        (groupHomology.inhomogeneousChains.d B (n + 1) x) = 0
      exact congrArg (fun f ↦ f x)
        (ModuleCat.hom_ext_iff.1
          (groupHomology.inhomogeneousChains.d_comp_d B n)))

/-- The concrete algebraic cycle group and the closed compact cycle group have
the same underlying additive group. -/
private def algebraicCyclesAddEquivCompactCycles (n : ℕ) :
    ((groupHomology.inhomogeneousChains B).sc'
      (n + 2) (n + 1) n).moduleCatLeftHomologyData.K ≃+
      kernelGroup (differential B hρ n) where
  toFun x := ⟨x.1, by
    change groupHomology.inhomogeneousChains.d B n x.1 = 0
    have hx := x.2
    change (groupHomology.inhomogeneousChains B).d
      (n + 1) n x.1 = 0 at hx
    rw [groupHomology.inhomogeneousChains.d_def] at hx
    exact hx⟩
  invFun x := ⟨x.1, by
    have hx := x.2
    change groupHomology.inhomogeneousChains.d B n x.1 = 0 at hx
    change (groupHomology.inhomogeneousChains B).d
      (n + 1) n x.1 = 0
    rw [groupHomology.inhomogeneousChains.d_def]
    exact hx⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  map_add' x y := by apply Subtype.ext; rfl

/-- The algebraic boundary range becomes the compact boundary range under the
cycle identification. -/
private lemma algebraicBoundaryRange_map (n : ℕ) :
    AddSubgroup.map
        (algebraicCyclesAddEquivCompactCycles B hρ n).toAddMonoidHom
        ((groupHomology.inhomogeneousChains B).sc'
          (n + 2) (n + 1) n).moduleCatLeftHomologyData.f'.hom.range.toAddSubgroup =
      (boundaryToKernel (differential B hρ (n + 1))
        (differential B hρ n) (fun x ↦ by
          change groupHomology.inhomogeneousChains.d B n
            (groupHomology.inhomogeneousChains.d B (n + 1) x) = 0
          exact congrArg (fun f ↦ f x)
            (ModuleCat.hom_ext_iff.1
              (groupHomology.inhomogeneousChains.d_comp_d B n)))).hom.range := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx⟩, rfl⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    have hx' := congrArg Subtype.val hx
    change (groupHomology.inhomogeneousChains B).d
      (n + 2) (n + 1) x = z.1 at hx'
    rw [groupHomology.inhomogeneousChains.d_def] at hx'
    exact hx'
  · rintro ⟨x, rfl⟩
    let e := algebraicCyclesAddEquivCompactCycles B hρ n
    let d := boundaryToKernel (differential B hρ (n + 1))
      (differential B hρ n) (fun x ↦ by
        change groupHomology.inhomogeneousChains.d B n
          (groupHomology.inhomogeneousChains.d B (n + 1) x) = 0
        exact congrArg (fun f ↦ f x)
          (ModuleCat.hom_ext_iff.1
            (groupHomology.inhomogeneousChains.d_comp_d B n)))
    let z : ((groupHomology.inhomogeneousChains B).sc'
        (n + 2) (n + 1) n).moduleCatLeftHomologyData.K :=
      ⟨groupHomology.inhomogeneousChains.d B (n + 1) x, by
        change (groupHomology.inhomogeneousChains B).d (n + 1) n
          (groupHomology.inhomogeneousChains.d B (n + 1) x) = 0
        rw [groupHomology.inhomogeneousChains.d_def]
        exact congrArg (fun f ↦ f x)
          (ModuleCat.hom_ext_iff.1
            (groupHomology.inhomogeneousChains.d_comp_d B n))⟩
    refine ⟨z, ?_, ?_⟩
    · refine ⟨x, ?_⟩
      apply Subtype.ext
      change (groupHomology.inhomogeneousChains B).d
        (n + 2) (n + 1) x = z.1
      rw [groupHomology.inhomogeneousChains.d_def]
    · rfl

/-- The underlying additive group of compact bar homology agrees with
mathlib's algebraic group homology. -/
noncomputable def groupHomologyAddEquivPositive (n : ℕ) :
    groupHomology B (n + 1) ≃+ positiveHomology B hρ n := by
  let K := groupHomology.inhomogeneousChains B
  let e : K.homology (n + 1) ≅
      (K.sc' (n + 2) (n + 1) n).moduleCatLeftHomologyData.H :=
    K.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp) ≪≫
      (K.sc' (n + 2) (n + 1) n).moduleCatHomologyIso
  exact e.toLinearEquiv.toAddEquiv |>.trans
    (QuotientAddGroup.congr
      (K.sc' (n + 2) (n + 1) n).moduleCatLeftHomologyData.f'.hom.range.toAddSubgroup
      (boundaryToKernel (differential B hρ (n + 1))
        (differential B hρ n) (fun x ↦ by
          change groupHomology.inhomogeneousChains.d B n
            (groupHomology.inhomogeneousChains.d B (n + 1) x) = 0
          exact congrArg (fun f ↦ f x)
            (ModuleCat.hom_ext_iff.1
              (groupHomology.inhomogeneousChains.d_comp_d B n)))).hom.range
      (algebraicCyclesAddEquivCompactCycles B hρ n)
      (algebraicBoundaryRange_map B hρ n))

/-- On a concrete algebraic cycle, the finite-bar comparison is represented
by the same cycle in compact homology. -/
private lemma groupHomologyAddEquivPositive_mk (n : ℕ)
    (x : ((groupHomology.inhomogeneousChains B).sc'
      (n + 2) (n + 1) n).moduleCatLeftHomologyData.K) :
    let K := groupHomology.inhomogeneousChains B
    let S := K.sc' (n + 2) (n + 1) n
    let z : K.cycles (n + 1) :=
      (K.cyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).inv
        (S.moduleCatCyclesIso.inv x)
    let xc : kernelGroup (differential B hρ n) := ⟨x.1, by
      change groupHomology.inhomogeneousChains.d B n x.1 = 0
      have hx := x.2
      change (groupHomology.inhomogeneousChains B).d (n + 1) n x.1 = 0 at hx
      rw [groupHomology.inhomogeneousChains.d_def] at hx
      exact hx⟩
    groupHomologyAddEquivPositive B hρ n (K.homologyπ (n + 1) z) =
      QuotientAddGroup.mk xc := by
  dsimp only
  let K := groupHomology.inhomogeneousChains B
  let S := K.sc' (n + 2) (n + 1) n
  let z : K.cycles (n + 1) :=
    (K.cyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).inv
      (S.moduleCatCyclesIso.inv x)
  have hsc :
      (K.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom
          (K.homologyπ (n + 1) z) =
        S.homologyπ (S.moduleCatCyclesIso.inv x) := by
    have h := ModuleCat.hom_ext_iff.1
      (K.π_homologyIsoSc'_hom (n + 2) (n + 1) n (by simp) (by simp))
    have hz := LinearMap.congr_fun h z
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
      Iso.inv_hom_id_apply, z, S] using hz
  have hmod :
      S.moduleCatHomologyIso.hom
          (S.homologyπ (S.moduleCatCyclesIso.inv x)) =
        S.moduleCatLeftHomologyData.π x := by
    have h := ModuleCat.hom_ext_iff.1 S.π_moduleCatCyclesIso_hom
    have hx := LinearMap.congr_fun h (S.moduleCatCyclesIso.inv x)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
      Iso.inv_hom_id_apply] using hx
  change
    (QuotientAddGroup.congr
      S.moduleCatLeftHomologyData.f'.hom.range.toAddSubgroup
      (boundaryToKernel (differential B hρ (n + 1))
        (differential B hρ n) _).hom.range
      (algebraicCyclesAddEquivCompactCycles B hρ n)
      (algebraicBoundaryRange_map B hρ n))
        (S.moduleCatHomologyIso.hom
          ((K.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom
            (K.homologyπ (n + 1) z))) = _
  rw [hsc, hmod]
  rfl

/-- The finite-bar comparison sends the class of an algebraic cycle to the
class of the same underlying bar chain in compact homology. -/
@[simp]
lemma groupHomologyAddEquivPositive_homologyπ (n : ℕ)
    (z : (groupHomology.inhomogeneousChains B).cycles (n + 1)) :
    groupHomologyAddEquivPositive B hρ n
        ((groupHomology.inhomogeneousChains B).homologyπ (n + 1) z) =
      QuotientAddGroup.mk
        (⟨(groupHomology.inhomogeneousChains B).iCycles (n + 1) z, by
          change groupHomology.inhomogeneousChains.d B n
            ((groupHomology.inhomogeneousChains B).iCycles (n + 1) z) = 0
          have h := ModuleCat.hom_ext_iff.1
            ((groupHomology.inhomogeneousChains B).iCycles_d (n + 1) n)
          rw [ModuleCat.hom_comp,
            groupHomology.inhomogeneousChains.d_def] at h
          have hz := LinearMap.congr_fun h z
          exact calc
            (groupHomology.inhomogeneousChains.d B n).hom
                (((groupHomology.inhomogeneousChains B).iCycles (n + 1)).hom z) =
              ((groupHomology.inhomogeneousChains.d B n).hom.comp
                ((groupHomology.inhomogeneousChains B).iCycles (n + 1)).hom) z := rfl
            _ = 0 := hz⟩ : kernelGroup (differential B hρ n)) := by
  let K := groupHomology.inhomogeneousChains B
  let S := K.sc' (n + 2) (n + 1) n
  let x : S.moduleCatLeftHomologyData.K :=
    S.moduleCatCyclesIso.hom
      ((K.cyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom z)
  let xc : kernelGroup (differential B hρ n) := ⟨x.1, by
    change groupHomology.inhomogeneousChains.d B n x.1 = 0
    have hx := x.2
    change (groupHomology.inhomogeneousChains B).d (n + 1) n x.1 = 0 at hx
    rw [groupHomology.inhomogeneousChains.d_def] at hx
    exact hx⟩
  have hx : x.1 = K.iCycles (n + 1) z := by
    have h₁ := ModuleCat.hom_ext_iff.1 S.moduleCatCyclesIso_hom_i
    rw [ModuleCat.hom_comp] at h₁
    have h₁z := LinearMap.congr_fun h₁
      ((K.cyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom z)
    rw [LinearMap.comp_apply] at h₁z
    have h₂ := ModuleCat.hom_ext_iff.1
      (K.cyclesIsoSc'_hom_iCycles (n + 2) (n + 1) n (by simp) (by simp))
    rw [ModuleCat.hom_comp] at h₂
    have h₂z := LinearMap.congr_fun h₂ z
    rw [LinearMap.comp_apply] at h₂z
    change S.moduleCatLeftHomologyData.i.hom
        (S.moduleCatCyclesIso.hom.hom
          ((K.cyclesIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).hom z)) =
      (K.iCycles (n + 1)).hom z
    exact h₁z.trans h₂z
  rw [show groupHomologyAddEquivPositive B hρ n (K.homologyπ (n + 1) z) =
      QuotientAddGroup.mk xc by
    simpa [x, xc, K, S] using groupHomologyAddEquivPositive_mk B hρ n x]
  apply congrArg QuotientAddGroup.mk
  exact Subtype.ext hx

end FiniteBar

end CompHausAddCommGrp

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [CompactSpace G]
variable (A : Rep.{u} R G) (L : LevelCompact A)

/-- The compact Hausdorff topology on the finite Tate stage in degree
`-(n + 2)`, obtained from the finite inhomogeneous bar complex for `G / S`
with coefficients in `A^S`.

This is a topology on the underlying additive group only.  In particular, it
does not assert a topological-module structure over `R`. -/
@[expose] noncomputable def finiteTateNegative (S : OpenNormalSubgroup G) (n : ℕ) :
    CompHausAddCommGrp.{u} := by
  letI : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
  letI : TopologicalSpace (A.quotientToInvariants S.toSubgroup) :=
    L.topology S.toOpenSubgroup
  letI : CompactSpace (A.quotientToInvariants S.toSubgroup) :=
    L.compact S.toOpenSubgroup
  letI : T2Space (A.quotientToInvariants S.toSubgroup) :=
    L.t2 S.toOpenSubgroup
  letI : IsTopologicalAddGroup (A.quotientToInvariants S.toSubgroup) :=
    L.topologicalAddGroup S.toOpenSubgroup
  exact CompHausAddCommGrp.FiniteBar.positiveHomology
    (A.quotientToInvariants S.toSubgroup)
    (continuous_quotientToInvariants_action A L S) n

/-- The compact negative Tate stage is the positive homology of the finite
bar complex with its levelwise compact coefficient topology. -/
lemma finiteTateNegative_eq_positiveHomology (S : OpenNormalSubgroup G) (n : ℕ) :
    finiteTateNegative A L S n =
      @CompHausAddCommGrp.FiniteBar.positiveHomology
        R (G ⧸ S.toSubgroup) _ _ (Fintype.ofFinite _)
        (A.quotientToInvariants S.toSubgroup)
        (L.topology S.toOpenSubgroup) (L.compact S.toOpenSubgroup)
        (L.t2 S.toOpenSubgroup) (L.topologicalAddGroup S.toOpenSubgroup)
        (continuous_quotientToInvariants_action A L S) n := rfl

/-- The canonical compact additive isomorphism from a negative Tate stage
to its finite-bar presentation. It transports continuous morphisms without
rewriting their source and target objects. -/
noncomputable def finiteTateNegativeIsoPositiveHomology
    (S : OpenNormalSubgroup G) (n : ℕ) :
    finiteTateNegative A L S n ≅
      @CompHausAddCommGrp.FiniteBar.positiveHomology
        R (G ⧸ S.toSubgroup) _ _ (Fintype.ofFinite _)
        (A.quotientToInvariants S.toSubgroup)
        (L.topology S.toOpenSubgroup) (L.compact S.toOpenSubgroup)
        (L.t2 S.toOpenSubgroup) (L.topologicalAddGroup S.toOpenSubgroup)
        (continuous_quotientToInvariants_action A L S) n :=
  eqToIso (finiteTateNegative_eq_positiveHomology A L S n)

/-- The algebraic finite-bar homology group and its compact finite-level model
have the same underlying additive group. -/
@[expose] noncomputable def groupHomologyAddEquivFiniteTateNegative
    (S : OpenNormalSubgroup G) (n : ℕ) :
    groupHomology (A.quotientToInvariants S.toSubgroup) (n + 1) ≃+
      finiteTateNegative A L S n := by
  letI : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
  letI : TopologicalSpace (A.quotientToInvariants S.toSubgroup) :=
    L.topology S.toOpenSubgroup
  letI : CompactSpace (A.quotientToInvariants S.toSubgroup) :=
    L.compact S.toOpenSubgroup
  letI : T2Space (A.quotientToInvariants S.toSubgroup) :=
    L.t2 S.toOpenSubgroup
  letI : IsTopologicalAddGroup (A.quotientToInvariants S.toSubgroup) :=
    L.topologicalAddGroup S.toOpenSubgroup
  exact (CompHausAddCommGrp.FiniteBar.groupHomologyAddEquivPositive
    (A.quotientToInvariants S.toSubgroup)
    (continuous_quotientToInvariants_action A L S) n).trans
      (((forget₂ CompHausAddCommGrp AddCommGrpCat).mapIso
        (finiteTateNegativeIsoPositiveHomology A L S n).symm).addCommGroupIsoToAddEquiv)

/-- The finite-level comparison is the finite-bar comparison followed by
the inverse of the canonical presentation isomorphism. -/
@[simp]
lemma groupHomologyAddEquivFiniteTateNegative_apply
    (S : OpenNormalSubgroup G) (n : ℕ)
    (x : groupHomology (A.quotientToInvariants S.toSubgroup) (n + 1)) :
    groupHomologyAddEquivFiniteTateNegative A L S n x =
      (finiteTateNegativeIsoPositiveHomology A L S n).inv
        (@CompHausAddCommGrp.FiniteBar.groupHomologyAddEquivPositive
          R (G ⧸ S.toSubgroup) _ _ (Fintype.ofFinite _)
          (A.quotientToInvariants S.toSubgroup)
          (L.topology S.toOpenSubgroup) (L.compact S.toOpenSubgroup)
          (L.t2 S.toOpenSubgroup) (L.topologicalAddGroup S.toOpenSubgroup)
          (continuous_quotientToInvariants_action A L S) n x) := rfl

/-- Algebraic Tate cohomology in degree `-(n + 2)` is additively equivalent
to its compact bar-homology presentation at the open normal level `S`.

The common universe is inherited from mathlib's finite-group Tate-to-homology
comparison.  This is an explicit additive equivalence, not a definitional
equality or a topological-module identification. -/
noncomputable def tateCohomologyNegativeAddEquivFiniteTate
    (S : OpenNormalSubgroup G) [Fintype (G ⧸ S.toSubgroup)] (n : ℕ) :
    tateCohomology (A.quotientToInvariants S.toSubgroup) (-(n + 2 : ℤ)) ≃+
      finiteTateNegative A L S n := by
  letI : TopologicalSpace (A.quotientToInvariants S.toSubgroup) :=
    L.topology S.toOpenSubgroup
  letI : CompactSpace (A.quotientToInvariants S.toSubgroup) :=
    L.compact S.toOpenSubgroup
  letI : T2Space (A.quotientToInvariants S.toSubgroup) :=
    L.t2 S.toOpenSubgroup
  letI : IsTopologicalAddGroup (A.quotientToInvariants S.toSubgroup) :=
    L.topologicalAddGroup S.toOpenSubgroup
  exact
    ((TateCohomology.isoGroupHomology (R := R) (G := G ⧸ S.toSubgroup)
      (-(n + 2 : ℤ)) (n + 1) (by omega)).app
        (A.quotientToInvariants S.toSubgroup)).toLinearEquiv.toAddEquiv |>.trans
      (CompHausAddCommGrp.FiniteBar.groupHomologyAddEquivPositive
        (A.quotientToInvariants S.toSubgroup)
        (continuous_quotientToInvariants_action A L S) n)

/-- Mathlib's Tate-to-homology equivalence followed by the compact finite-level
comparison agrees with the Tate-to-compact comparison. The supplied quotient
`Fintype` in the Tate group is reconciled with the canonical finite-bar one. -/
lemma tateCohomologyNegativeAddEquivFiniteTate_coherence
    (S : OpenNormalSubgroup G) [fp : Fintype (G ⧸ S.toSubgroup)] (n : ℕ) :
    (((TateCohomology.isoGroupHomology (R := R) (G := G ⧸ S.toSubgroup)
      (-(n + 2 : ℤ)) (n + 1) (by omega)).app
        (A.quotientToInvariants S.toSubgroup)).toLinearEquiv.toAddEquiv).trans
          (groupHomologyAddEquivFiniteTateNegative A L S n) =
      tateCohomologyNegativeAddEquivFiniteTate A L S n := by
  have hfp : fp = Fintype.ofFinite (G ⧸ S.toSubgroup) := Subsingleton.elim _ _
  cases hfp
  rfl

/-- A Tate class transported through mathlib's homology comparison has the
same compact value as under the Tate-to-compact equivalence. -/
@[simp]
lemma groupHomologyAddEquivFiniteTateNegative_isoGroupHomology_apply
    (S : OpenNormalSubgroup G) [Fintype (G ⧸ S.toSubgroup)] (n : ℕ)
    (x : tateCohomology (A.quotientToInvariants S.toSubgroup) (-(n + 2 : ℤ))) :
    groupHomologyAddEquivFiniteTateNegative A L S n
        (((TateCohomology.isoGroupHomology (R := R) (G := G ⧸ S.toSubgroup)
          (-(n + 2 : ℤ)) (n + 1) (by omega)).app
            (A.quotientToInvariants S.toSubgroup)).hom x) =
      tateCohomologyNegativeAddEquivFiniteTate A L S n x :=
  congrArg (fun e ↦ e x) (tateCohomologyNegativeAddEquivFiniteTate_coherence A L S n)

end ContinuousGroupCohomology.LevelCompact
