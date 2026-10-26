/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.QuotientTransitions
public import ContinuousGroupCohomology.SeededCochains
public import ContinuousGroupCohomology.Algebra.Category.ModuleCat.Topology.HomologyBoundary
public import ContinuousGroupCohomology.CompactDiscreteTorsion

set_option warningAsError true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Finite-stage detection of zero continuous-cohomology classes

A class at an open-normal quotient stage whose inflation vanishes becomes zero
after a class-dependent refinement. Positive degrees descend an actual boundary
cochain; degree zero is already detected at the original stage.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

set_option backward.isDefEq.respectTransparency false in
private theorem homologyπ_succ_eq_zero_iff_boundary
    (K : CochainComplex (TopModuleCat k) ℕ) (n : ℕ) (z : K.cycles (n + 1)) :
    (K.homologyπ (n + 1)).hom z = 0 ↔
      ∃ w : K.X n, (K.d n (n + 1)).hom w = (K.iCycles (n + 1)).hom z := by
  let S := K.sc' n (n + 1) (n + 2)
  have hp : (ComplexShape.up ℕ).prev (n + 1) = n := CochainComplex.prev_nat_succ n
  have hn : (ComplexShape.up ℕ).next (n + 1) = n + 2 := by
    rw [CochainComplex.next]
    omega
  let cyclesIso := K.cyclesIsoSc' n (n + 1) (n + 2) hp hn
  let homologyIso := K.homologyIsoSc' n (n + 1) (n + 2) hp hn
  let : PreservesLimitsOfShape WalkingCospan (forget (TopModuleCat k)) := by
    rw [← HasForget₂.forget_comp (C := TopModuleCat k) (D := TopCat)]
    infer_instance
  have hcycles_inj : Function.Injective cyclesIso.hom.hom :=
    ConcreteCategory.injective_of_mono_of_preservesPullback cyclesIso.hom
  have hhomology_inj : Function.Injective homologyIso.hom.hom :=
    ConcreteCategory.injective_of_mono_of_preservesPullback homologyIso.hom
  have hπcomp : (K.homologyπ (n + 1)).hom z = 0 ↔
      S.homologyπ.hom (cyclesIso.hom.hom z) = 0 := by
    have h := congrArg (fun f : K.cycles (n + 1) ⟶ S.homology => f.hom z)
      (K.π_homologyIsoSc'_hom n (n + 1) (n + 2) hp hn)
    constructor
    · intro hz
      simpa only [ConcreteCategory.comp_apply, hz, map_zero] using h.symm
    · intro hz
      apply hhomology_inj
      simpa only [ConcreteCategory.comp_apply, map_zero] using h.trans hz
  have hto : ∀ w : K.X n,
      (ConcreteCategory.hom cyclesIso.hom)
        ((ConcreteCategory.hom (K.toCycles n (n + 1))) w) =
          S.toCycles.hom w := by
    intro w
    have h := congrArg (fun f : K.X n ⟶ S.cycles => f.hom w)
      (K.toCycles_cyclesIsoSc'_hom n (n + 1) (n + 2) hp hn)
    change (ConcreteCategory.hom cyclesIso.hom)
      ((ConcreteCategory.hom (K.toCycles n (n + 1))) w) = S.toCycles.hom w at h
    exact h
  have hboundary : ∀ w : K.X n,
      (K.d n (n + 1)).hom w = (K.iCycles (n + 1)).hom z ↔
        (K.toCycles n (n + 1)).hom w = z := by
    intro w
    constructor
    · intro hw
      apply (ConcreteCategory.injective_of_mono_of_preservesPullback (K.iCycles (n + 1)))
      have h := congrArg (fun f : K.X n ⟶ K.X (n + 1) => f.hom w)
        (K.toCycles_i n (n + 1))
      have hh : (K.iCycles (n + 1)).hom ((K.toCycles n (n + 1)).hom w) =
          (K.d n (n + 1)).hom w := by
        simpa only [ConcreteCategory.comp_apply] using h
      exact hh.trans hw
    · intro hw
      have h := congrArg (fun f : K.X n ⟶ K.X (n + 1) => f.hom w)
        (K.toCycles_i n (n + 1))
      have hh : (K.iCycles (n + 1)).hom ((K.toCycles n (n + 1)).hom w) =
          (K.d n (n + 1)).hom w := by
        simpa only [ConcreteCategory.comp_apply] using h
      exact hh.symm.trans
        (congrArg (K.iCycles (n + 1)).hom hw)
  constructor
  · intro hz
    obtain ⟨w, hw⟩ :=
      (TopModuleCat.shortComplex_homologyπ_eq_zero_iff S (cyclesIso.hom.hom z)).mp
        (hπcomp.mp hz)
    refine ⟨w, (hboundary w).mpr ?_⟩
    apply hcycles_inj
    rw [hto]
    exact hw
  · rintro ⟨w, hw⟩
    apply hπcomp.mpr
    apply (TopModuleCat.shortComplex_homologyπ_eq_zero_iff S (cyclesIso.hom.hom z)).mpr
    exact ⟨w, (hto w).symm.trans (congrArg cyclesIso.hom.hom ((hboundary w).mp hw))⟩

/-- Degree-zero inflation detects a zero class already at the original stage. -/
theorem class_eq_zero_of_inflation_zero_degree_zero (M : OpenNormalSubgroup G)
    (X : TopRep.{max v w} k G)
    (a : continuousCohomology 0 (TopRep.quotientInvariants M.toSubgroup X))
    (ha : (map (openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X) 0).hom a = 0) : a = 0 := by
  let YM := TopRep.quotientInvariants M.toSubgroup X
  obtain ⟨zM, rfl⟩ := π_surjective YM 0 a
  have hπG : (π X 0).hom
      ((cocyclesMap (openNormalQuotientHom M)
        (TopRep.quotientInvariantsIncl M.toSubgroup X) 0).hom zM) = 0 := by
    have h := congrArg
      (fun f : cocycles YM 0 ⟶ continuousCohomology 0 X => f.hom zM)
      (π_map (openNormalQuotientHom M)
        (TopRep.quotientInvariantsIncl M.toSubgroup X) 0)
    calc
      _ = (map (openNormalQuotientHom M)
          (TopRep.quotientInvariantsIncl M.toSubgroup X) 0).hom ((π YM 0).hom zM) := by
        simpa only [ConcreteCategory.comp_apply] using h.symm
      _ = 0 := ha
  have hπinj : Function.Injective (π X 0).hom := by
    let : PreservesLimitsOfShape WalkingCospan (forget (TopModuleCat k)) := by
      rw [← HasForget₂.forget_comp (C := TopModuleCat k) (D := TopCat)]
      infer_instance
    exact ConcreteCategory.injective_of_mono_of_preservesPullback (π X 0)
  have hzM : zM = 0 := by
    apply cocyclesMap_injective (openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X)
      (QuotientGroup.mk'_surjective M.toSubgroup) Subtype.val_injective 0
    simpa only [map_zero] using hπinj (by simpa only [map_zero] using hπG)
  rw [hzM, map_zero]

variable (X : TopRep.{max v w} k G) [CompactSpace G] [DiscreteTopology X]

/-- A class which becomes zero on the full compact group is already zero at a
possibly finer open-normal quotient stage. The refinement depends on the class. -/
theorem exists_refinement_class_eq_zero (M : OpenNormalSubgroup G) (degree : ℕ)
    (a : continuousCohomology degree (TopRep.quotientInvariants M.toSubgroup X))
    (ha : (map (openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X) degree).hom a = 0) :
    ∃ (N : OpenNormalSubgroup G) (hNM : N ≤ M),
      (map (quotientTransitionHom N M hNM)
        (quotientTransitionIncl X hNM) degree).hom a = 0 := by
  let YM := TopRep.quotientInvariants M.toSubgroup X
  let CM := TopRep.homogeneousCochains YM
  let C := TopRep.homogeneousCochains X
  cases degree with
  | zero =>
    have hzM := class_eq_zero_of_inflation_zero_degree_zero M X a ha
    refine ⟨M, le_refl M, ?_⟩
    rw [quotientTransition_map_id X M 0]
    simp only [hzM, map_zero]
  | succ n =>
    obtain ⟨zM, rfl⟩ := π_surjective YM (n + 1) a
    have hπG : (π X (n + 1)).hom
        ((cocyclesMap (openNormalQuotientHom M)
          (TopRep.quotientInvariantsIncl M.toSubgroup X) (n + 1)).hom zM) = 0 := by
      have h := congrArg
        (fun f : cocycles YM (n + 1) ⟶ continuousCohomology (n + 1) X => f.hom zM)
        (π_map (openNormalQuotientHom M)
          (TopRep.quotientInvariantsIncl M.toSubgroup X) (n + 1))
      calc
        _ = (map (openNormalQuotientHom M)
            (TopRep.quotientInvariantsIncl M.toSubgroup X) (n + 1)).hom
              ((π YM (n + 1)).hom zM) := by
          simpa only [ConcreteCategory.comp_apply] using h.symm
        _ = 0 := ha
    obtain ⟨wG, hboundaryG⟩ :=
      (homologyπ_succ_eq_zero_iff_boundary C n
        ((cocyclesMap (openNormalQuotientHom M)
          (TopRep.quotientInvariantsIncl M.toSubgroup X) (n + 1)).hom zM)).mp hπG
    obtain ⟨N, hNM, wN, hwN⟩ := exists_quotient_cochain_lift_below X M n wG
    let YN := TopRep.quotientInvariants N.toSubgroup X
    let CN := TopRep.homogeneousCochains YN
    let zN : cocycles YN (n + 1) :=
      (cocyclesMap (quotientTransitionHom N M hNM)
        (quotientTransitionIncl X hNM) (n + 1)).hom zM
    have hmapZ :
        ((cochainsMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X)).f (n + 1)).hom
          ((CN.iCycles (n + 1)).hom zN) =
        (C.iCycles (n + 1)).hom
          ((cocyclesMap (openNormalQuotientHom M)
            (TopRep.quotientInvariantsIncl M.toSubgroup X) (n + 1)).hom zM) := by
      calc
        _ = (C.iCycles (n + 1)).hom
            ((cocyclesMap (openNormalQuotientHom N)
              (TopRep.quotientInvariantsIncl N.toSubgroup X) (n + 1)).hom zN) := by
          have h := congrArg
            (fun f : cocycles YN (n + 1) ⟶ C.X (n + 1) => f.hom zN)
            (HomologicalComplex.cyclesMap_i (cochainsMap (openNormalQuotientHom N)
              (TopRep.quotientInvariantsIncl N.toSubgroup X)) (n + 1))
          simpa only [ConcreteCategory.comp_apply] using h.symm
        _ = (C.iCycles (n + 1)).hom
            ((cocyclesMap (openNormalQuotientHom M)
              (TopRep.quotientInvariantsIncl M.toSubgroup X) (n + 1)).hom zM) := by
          have h := congrArg (fun f : CM ⟶ C =>
              (HomologicalComplex.cyclesMap f (n + 1)).hom zM)
            (quotientTransition_cochainsMap_inflate X hNM)
          simpa only [HomologicalComplex.cyclesMap_comp, ConcreteCategory.comp_apply] using
            congrArg (C.iCycles (n + 1)).hom h.symm
    have hreflect : (CN.d n (n + 1)).hom wN =
        (CN.iCycles (n + 1)).hom zN := by
      apply cochainsMap_injective (openNormalQuotientHom N)
        (TopRep.quotientInvariantsIncl N.toSubgroup X)
        (QuotientGroup.mk'_surjective N.toSubgroup) Subtype.val_injective (n + 1)
      calc
        ((cochainsMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X)).f (n + 1)).hom
            ((CN.d n (n + 1)).hom wN) =
            (C.d n (n + 1)).hom
              (((cochainsMap (openNormalQuotientHom N)
                (TopRep.quotientInvariantsIncl N.toSubgroup X)).f n).hom wN) := by
          have h := congrArg (fun f => f.hom wN)
            ((cochainsMap (openNormalQuotientHom N)
              (TopRep.quotientInvariantsIncl N.toSubgroup X)).comm n (n + 1))
          simpa only [ConcreteCategory.comp_apply] using h.symm
        _ = (C.d n (n + 1)).hom wG := by rw [hwN]
        _ = _ := hboundaryG
        _ = _ := hmapZ.symm
    have hcycles : (CN.toCycles n (n + 1)).hom wN = zN := by
      let : PreservesLimitsOfShape WalkingCospan (forget (TopModuleCat k)) := by
        rw [← HasForget₂.forget_comp (C := TopModuleCat k) (D := TopCat)]
        infer_instance
      apply (ConcreteCategory.injective_of_mono_of_preservesPullback (CN.iCycles (n + 1)))
      calc
        (CN.iCycles (n + 1)).hom ((CN.toCycles n (n + 1)).hom wN) =
            (CN.d n (n + 1)).hom wN := by
          rw [← CN.toCycles_i n (n + 1)]
          rfl
        _ = _ := hreflect
    have hπN : (π YN (n + 1)).hom zN = 0 :=
      (homologyπ_succ_eq_zero_iff_boundary CN n zN).mpr ⟨wN, hreflect⟩
    refine ⟨N, hNM, ?_⟩
    have h := congrArg
      (fun f : cocycles YM (n + 1) ⟶ continuousCohomology (n + 1) YN => f.hom zM)
      (π_map (quotientTransitionHom N M hNM) (quotientTransitionIncl X hNM) (n + 1))
    simpa only [ConcreteCategory.comp_apply] using h.trans hπN

/-- Equality after inflation is detected after a class-dependent common
refinement of the original stage. -/
theorem exists_refinement_class_eq_of_inflation_eq (M : OpenNormalSubgroup G)
    (degree : ℕ)
    (a b : continuousCohomology degree (TopRep.quotientInvariants M.toSubgroup X))
    (hab : (map (openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X) degree).hom a =
      (map (openNormalQuotientHom M)
        (TopRep.quotientInvariantsIncl M.toSubgroup X) degree).hom b) :
    ∃ (N : OpenNormalSubgroup G) (hNM : N ≤ M),
      (map (quotientTransitionHom N M hNM)
        (quotientTransitionIncl X hNM) degree).hom a =
      (map (quotientTransitionHom N M hNM)
        (quotientTransitionIncl X hNM) degree).hom b := by
  have hzero : (map (openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X) degree).hom (a - b) = 0 := by
    let f := map (openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X) degree
    change f.hom (a - b) = 0
    change f.hom a = f.hom b at hab
    rw [map_sub, sub_eq_zero]
    exact hab
  let diff := a - b
  have hvanish := exists_refinement_class_eq_zero X M degree diff hzero
  obtain ⟨N, hNM, hz⟩ := hvanish
  refine ⟨N, hNM, ?_⟩
  let f := map (quotientTransitionHom N M hNM) (quotientTransitionIncl X hNM) degree
  change f.hom (a - b) = 0 at hz
  change f.hom a = f.hom b
  simpa only [map_sub, sub_eq_zero] using hz

end ContinuousCohomology
