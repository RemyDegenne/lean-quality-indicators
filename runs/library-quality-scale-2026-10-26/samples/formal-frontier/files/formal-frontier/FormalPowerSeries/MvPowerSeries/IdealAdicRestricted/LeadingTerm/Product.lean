/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.ValuationResidue
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

public section

/-!
# Intrinsic leading exponent of a product

The intrinsic exponent of a product of nonzero principal-adically restricted
series is the sum of the intrinsic exponents. This only needs Hausdorffness,
not adic completeness or primitivity.
-/

set_option warningAsError true

namespace MonomialOrder

open MvPowerSeries

variable {σ R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    (μ : MonomialOrder σ) (a : R)
    [IsHausdorff (Ideal.span {a} : Ideal R) R]
    (ham : a ∈ IsLocalRing.maximalIdeal R)

/-- Nonzero restricted series multiply to a nonzero series, whose intrinsic
leading exponent is additive. The assertion concerns the *normalized residue*
exponents, not multiplication of actual leading coefficients in `R`. -/
theorem restrictedLeadingExponent_mul_of_ne_zero
    (f g : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
    (hf : f ≠ 0) (hg : g ≠ 0) :
    f * g ≠ 0 ∧
      μ.restrictedLeadingExponent a ham (f * g) =
        μ.restrictedLeadingExponent a ham f + μ.restrictedLeadingExponent a ham g := by
  classical
  let coefficient (z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}))
      (index : σ →₀ ℕ) := coeff index (z : MvPowerSeries σ R)
  obtain ⟨indexF, F, hcontentF, hfactorF, honeF⟩ :=
    exists_restricted_content_factor a f
  obtain ⟨indexG, G, hcontentG, hfactorG, honeG⟩ :=
    exists_restricted_content_factor a g
  let c := coefficient f indexF
  let d := coefficient g indexG
  have hc : c ≠ 0 := coeff_ne_zero_of_generates_content a f hf indexF hcontentF
  have hd : d ≠ 0 := coeff_ne_zero_of_generates_content a g hg indexG hcontentG
  have hF : restrictedResidue a ham F ≠ 0 :=
    restrictedResidue_ne_zero_of_coeff_one a ham F indexF honeF
  have hG : restrictedResidue a ham G ≠ 0 :=
    restrictedResidue_ne_zero_of_coeff_one a ham G indexG honeG
  have hres : restrictedResidue a ham (F * G) ≠ 0 := by
    rw [restrictedResidue_mul]
    exact mul_ne_zero hF hG
  let U := F * G
  have hU : U ≠ 0 := by
    intro hzero
    apply hres
    change restrictedResidue a ham U = 0
    rw [hzero]
    exact restrictedResidue_zero (σ := σ) a ham
  have hprimitive : Ideal.span (Set.range (fun index : σ →₀ ℕ =>
      coeff index (U : MvPowerSeries σ R))) = ⊤ := by
    have hunit : IsUnit (coeff (μ.degree (restrictedResidue a ham U))
        (U : MvPowerSeries σ R)) :=
      isUnit_coeff_degree_restrictedResidue a ham μ U hres
    obtain ⟨factor, hfactor⟩ := isUnit_iff_dvd_one.mp hunit
    apply (Ideal.eq_top_iff_one _).mpr
    have hmem : coeff (μ.degree (restrictedResidue a ham U))
        (U : MvPowerSeries σ R) ∈
        Ideal.span (Set.range (fun index : σ →₀ ℕ =>
          coeff index (U : MvPowerSeries σ R))) :=
      Ideal.subset_span (Set.mem_range_self _)
    rw [hfactor]
    simpa only [smul_eq_mul, mul_comm] using
      (Ideal.span (Set.range (fun index : σ →₀ ℕ =>
        coeff index (U : MvPowerSeries σ R)))).smul_mem factor hmem
  let indexU := restrictedContentIndex a U
  let H := restrictedContentFactor a U
  let t := coefficient U indexU
  have ht : IsUnit t := isUnit_restrictedContentCoefficient_of_primitive a U hprimitive
  have hUfactor : (U : MvPowerSeries σ R) = C t * (H : MvPowerSeries σ R) :=
    (restrictedContentFactor_spec a U).2.1
  have hfg : (f * g : MvPowerSeries σ R) = C (c * d) * (U : MvPowerSeries σ R) := by
    rw [hfactorF, hfactorG]
    simp only [U, Subring.coe_mul, map_mul]
    ring
  have hactual : coeff indexU (f * g : MvPowerSeries σ R) = c * d * t := by
    rw [hfg, coeff_C_mul]
  have hfactorProduct : (f * g : MvPowerSeries σ R) =
      C (coeff indexU (f * g : MvPowerSeries σ R)) *
        (H : MvPowerSeries σ R) := by
    calc
      (f * g : MvPowerSeries σ R) = C (c * d) * (U : MvPowerSeries σ R) := hfg
      _ = C (c * d) * (C t * (H : MvPowerSeries σ R)) := by rw [hUfactor]
      _ = C (coeff indexU (f * g : MvPowerSeries σ R)) *
            (H : MvPowerSeries σ R) := by
        rw [hactual]
        simp only [map_mul]
        ring
  have hcontentProduct : Ideal.span (Set.range (fun index : σ →₀ ℕ =>
      coeff index (f * g : MvPowerSeries σ R))) =
      Ideal.span {coeff indexU (f * g : MvPowerSeries σ R)} := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨index, rfl⟩
      have hcoeff : coeff index (f * g : MvPowerSeries σ R) =
          coeff indexU (f * g : MvPowerSeries σ R) *
            coeff index (H : MvPowerSeries σ R) := by
        calc
          coeff index (f * g : MvPowerSeries σ R) =
              coeff index (C (coeff indexU (f * g : MvPowerSeries σ R)) *
                (H : MvPowerSeries σ R)) := congrArg (coeff index) hfactorProduct
          _ = _ := by rw [coeff_C_mul]
      change coeff index (f * g : MvPowerSeries σ R) ∈
        Ideal.span {coeff indexU (f * g : MvPowerSeries σ R)}
      rw [hcoeff]
      exact Ideal.mem_span_singleton.mpr ⟨coeff index (H : MvPowerSeries σ R), rfl⟩
    · apply Ideal.span_le.mpr
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact Ideal.subset_span (Set.mem_range_self indexU)
  have hproduct : f * g ≠ 0 := by
    intro hzero
    have hcoeff : coeff indexU (f * g : MvPowerSeries σ R) = 0 := by
      have hraw : (f * g : MvPowerSeries σ R) = 0 :=
        congrArg (fun z : adicallyRestrictedSubring (σ := σ) (Ideal.span {a}) =>
          (z : MvPowerSeries σ R)) hzero
      simp only [hraw, map_zero]
    exact (mul_ne_zero (mul_ne_zero hc hd) ht.ne_zero) (hactual.symm.trans hcoeff)
  have hsupport := restrictedResidue_support_eq_of_unit_factor a ham U H t ht hUfactor
  have hdegree : μ.degree (restrictedResidue a ham H) =
      μ.degree (restrictedResidue a ham U) := by
    simp only [MonomialOrder.degree, hsupport]
  refine ⟨hproduct, ?_⟩
  rw [μ.restrictedLeadingExponent_eq_degree_of_content_factor a ham (f * g)
    hproduct indexU H hcontentProduct hfactorProduct,
    μ.restrictedLeadingExponent_eq_degree_of_content_factor a ham f hf indexF F
      hcontentF hfactorF,
    μ.restrictedLeadingExponent_eq_degree_of_content_factor a ham g hg indexG G
      hcontentG hfactorG, hdegree, restrictedResidue_mul]
  exact μ.degree_mul hF hG

end MonomialOrder
