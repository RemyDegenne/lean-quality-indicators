/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.IdealChange
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

public section

/-!
# A common monic parameter for a finite family of restricted series

For primitive restricted series over a valuation domain, one principal ideal
simultaneously preserves their leading exponents modulo the maximal ideal and
makes their unit-normalized reductions monic. No finiteness of variables or
completeness hypothesis is required.
-/

set_option warningAsError true

namespace MvPowerSeries

open scoped MonomialOrder

variable {σ R : Type*} [CommRing R]

private theorem exists_polynomial_mod (I : Ideal R) (f : MvPowerSeries σ R)
    (hf : IsAdicallyRestricted I f) :
    ∃ p : MvPolynomial σ (R ⧸ I),
      ∀ d, p.coeff d = Ideal.Quotient.mk I (coeff d f) := by
  classical
  have hfin : {d : σ →₀ ℕ | coeff d f ∉ I}.Finite := by
    simpa only [Submodule.pow_one] using hf 1
  let s := hfin.toFinset
  refine ⟨truncFinset (R ⧸ I) s (map (Ideal.Quotient.mk I) f), fun d => ?_⟩
  by_cases hd : d ∈ s
  · simp only [coeff_truncFinset_of_mem _ hd, coeff_map]
  · have hmem : coeff d f ∈ I := by
      by_contra hnot
      exact hd (hfin.mem_toFinset.mpr hnot)
    simpa only [coeff_truncFinset_eq_zero _ hd] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr hmem).symm

private theorem finite_divisor {α : Type*} [PreValuationRing R]
    (c : α → R) (s : Finset α) (hs : s.Nonempty) :
    ∃ j ∈ s, ∀ k ∈ s, c j ∣ c k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
    by_cases h : s.Nonempty
    · obtain ⟨j, hj, hdiv⟩ := ih h
      by_cases hja : c j ∣ c a
      · refine ⟨j, Finset.mem_insert_of_mem hj, ?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact hja
        · exact hdiv k hk
      · have haj := (ValuationRing.dvd_total (c a) (c j)).resolve_right hja
        refine ⟨a, by simp, ?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact dvd_refl _
        · exact haj.trans (hdiv k hk)
    · refine ⟨a, by simp, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact dvd_refl _
      · exact (h ⟨k, hk⟩).elim

/-- A finite family of primitive restricted series admits a common principal
parameter whose unit-normalized polynomial reductions are monic at their
original maximal-ideal leading exponents. -/
theorem exists_common_monic_parameter {ι : Type*} [Finite ι]
    [IsDomain R] [ValuationRing R] (μ : MonomialOrder σ) (a : R)
    (ha : a ≠ 0) (ham : a ∈ IsLocalRing.maximalIdeal R)
    (hrad : (Ideal.span {a}).radical = IsLocalRing.maximalIdeal R)
    (g : ι → MvPowerSeries σ R)
    (hg : ∀ i, IsAdicallyRestricted (Ideal.span {a}) (g i))
    (hprim : ∀ i, Ideal.span (Set.range (fun d : σ →₀ ℕ => coeff d (g i))) = ⊤) :
    ∃ (p : ι → MvPolynomial σ (R ⧸ IsLocalRing.maximalIdeal R))
      (b : R) (N : ℕ) (u : ι → Rˣ),
      (∀ i d, (p i).coeff d =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (coeff d (g i))) ∧
      (∀ i, p i ≠ 0) ∧ b ≠ 0 ∧ b ∈ IsLocalRing.maximalIdeal R ∧ 1 ≤ N ∧
      Ideal.span {a} ≤ Ideal.span {b} ∧
      (Ideal.span {b} : Ideal R) ^ N ≤ Ideal.span {a} ∧
      ∀ i, (u i : R) = coeff (μ.degree (p i)) (g i) ∧
        ∃ h : adicallyRestrictedSubring (σ := σ) (Ideal.span {b}),
          (h : MvPowerSeries σ R) = C (↑((u i)⁻¹) : R) * g i ∧
          μ.Monic (adicReduction (Ideal.span {b}) 1 h) ∧
          μ.degree (adicReduction (Ideal.span {b}) 1 h) = μ.degree (p i) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let m : Ideal R := IsLocalRing.maximalIdeal R
  let A : Ideal R := Ideal.span {a}
  have hm : m ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hAm : A ≤ m := by
    change Ideal.span {a} ≤ IsLocalRing.maximalIdeal R
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ham)
  let p : ι → MvPolynomial σ (R ⧸ m) := fun i =>
    Classical.choose (exists_polynomial_mod m (g i) ((hg i).mono hAm))
  have hp (i : ι) (d : σ →₀ ℕ) : (p i).coeff d = Ideal.Quotient.mk m (coeff d (g i)) :=
    Classical.choose_spec (exists_polynomial_mod m (g i) ((hg i).mono hAm)) d
  have hpne (i : ι) : p i ≠ 0 := by
    intro hzero
    have hcoeff (d : σ →₀ ℕ) : coeff d (g i) ∈ m := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← hp i d, hzero]
      simp
    have htop : (⊤ : Ideal R) ≤ m := by
      rw [← hprim i]
      exact Ideal.span_le.mpr (by rintro _ ⟨d, rfl⟩; exact hcoeff d)
    exact hm (top_le_iff.mp htop)
  have hunit (i : ι) : IsUnit (coeff (μ.degree (p i)) (g i)) := by
    have hc : (p i).coeff (μ.degree (p i)) ≠ 0 :=
      (μ.leadingCoeff_ne_zero_iff).mpr (hpne i)
    have hnot : coeff (μ.degree (p i)) (g i) ∉ m := by
      intro hmem
      exact hc (by rw [hp]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
    exact not_not.mp (by simpa only [m, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] using hnot)
  let u : ι → Rˣ := fun i => (hunit i).unit
  have hu (i : ι) : (u i : R) = coeff (μ.degree (p i)) (g i) :=
    (hunit i).unit_spec
  let t : Finset R := insert a <|
    Finset.univ.biUnion (fun i : ι =>
      ((hg i 1).toFinset.filter (fun d => μ.toSyn (μ.degree (p i)) < μ.toSyn d)).image
        (fun d => coeff d (g i)))
  have hat : a ∈ t := Finset.mem_insert_self _ _
  obtain ⟨b, hbt, hdiv⟩ := finite_divisor (R := R) id t ⟨a, hat⟩
  have hbt_cases : b = a ∨ ∃ i : ι, ∃ d : σ →₀ ℕ,
      μ.toSyn (μ.degree (p i)) < μ.toSyn d ∧ coeff d (g i) ∉ A ∧
        b = coeff d (g i) := by
    rcases Finset.mem_insert.mp hbt with h | h
    · exact Or.inl h
    · obtain ⟨i, -, himage⟩ := Finset.mem_biUnion.mp h
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp himage
      obtain ⟨hindex, hdegree⟩ := Finset.mem_filter.mp hd
      right
      refine ⟨i, d, hdegree, ?_, rfl⟩
      simpa only [A, Submodule.pow_one, Set.mem_ofPred_eq] using
        ((hg i 1).mem_toFinset.mp hindex)
  have hbnz : b ≠ 0 := by
    rcases hbt_cases with rfl | ⟨i, d, -, hd, rfl⟩
    · exact ha
    · intro hzero
      exact hd (hzero ▸ (Ideal.zero_mem A))
  have hbm : b ∈ m := by
    rcases hbt_cases with rfl | ⟨i, d, hdegree, -, rfl⟩
    · exact ham
    · apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← hp i d]
      exact μ.coeff_eq_zero_of_lt hdegree
  have hAb : A ≤ Ideal.span {b} :=
    Ideal.span_singleton_le_span_singleton.mpr (hdiv a hat)
  have hhigh (i : ι) (d : σ →₀ ℕ) (hd : μ.degree (p i) ≺[μ] d) :
      coeff d (g i) ∈ Ideal.span {b} := by
    by_cases hc : coeff d (g i) ∈ A
    · exact hAb hc
    · apply Ideal.mem_span_singleton.mpr
      apply hdiv
      apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨d, Finset.mem_filter.mpr ⟨?_, hd⟩, rfl⟩
      apply (hg i 1).mem_toFinset.mpr
      simpa only [A, Submodule.pow_one, Set.mem_ofPred_eq] using hc
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b ^ n ∈ A := by
    apply Ideal.mem_radical_iff.mp
    rw [hrad]
    exact hbm
  have hnzero : n ≠ 0 := by
    intro hn0
    subst n
    have htop : (1 : R) ∈ m := hAm (by simpa using hn)
    exact hm (m.eq_top_iff_one.mpr htop)
  have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hnzero
  have hpow : (Ideal.span {b} : Ideal R) ^ n ≤ A := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.span_le.mpr (by simpa using hn)
  refine ⟨p, b, n, u, hp, hpne, hbnz, hbm, hnpos, hAb, hpow, ?_⟩
  intro i
  refine ⟨hu i, ?_⟩
  let B : Ideal R := Ideal.span {b}
  have hgr : IsAdicallyRestricted B (g i) := (hg i).mono hAb
  have hscaled : IsAdicallyRestricted B (C (↑((u i)⁻¹) : R) * g i) := by
    intro k
    exact (hgr k).subset (by
      intro d hd hmem
      exact hd (by simpa only [coeff_C_mul] using
        (B ^ k).mul_mem_left (↑((u i)⁻¹) : R) hmem))
  let h : adicallyRestrictedSubring (σ := σ) B :=
    ⟨C (↑((u i)⁻¹) : R) * g i, (mem_adicallyRestrictedSubring B _).mpr hscaled⟩
  refine ⟨h, rfl, ?_⟩
  let q : MvPolynomial σ (R ⧸ B ^ 1) := adicReduction B 1 h
  have hqone : q.coeff (μ.degree (p i)) = 1 := by
    simp only [q, coeff_adicReduction, h, coeff_C_mul, ← hu i,
      Units.inv_mul, map_one]
  have hqle : μ.degree q ≼[μ] μ.degree (p i) := by
    apply (μ.degree_le_iff).mpr
    intro d hd
    by_contra hnot
    have hgt : μ.degree (p i) ≺[μ] d := lt_of_not_ge hnot
    have hzero : q.coeff d = 0 := by
      simp only [q, coeff_adicReduction]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simpa only [Submodule.pow_one, h, Subtype.coe_mk, coeff_C_mul] using
        (B.mul_mem_left (↑((u i)⁻¹) : R) (hhigh i d hgt))
    exact (MvPolynomial.mem_support_iff.mp hd) hzero
  have hqge : μ.degree (p i) ≼[μ] μ.degree q := by
    apply μ.le_degree
    apply MvPolynomial.mem_support_iff.mpr
    rw [hqone]
    intro hzero
    have hBmem : (1 : R) ∈ B := by
      have hJmem : (1 : R) ∈ B ^ 1 := Ideal.Quotient.eq_zero_iff_mem.mp
        (by simpa using hzero)
      simpa only [Submodule.pow_one] using hJmem
    have hBm : B ≤ m := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hbm)
    exact hm (m.eq_top_iff_one.mpr (hBm hBmem))
  have hdeg : μ.degree q = μ.degree (p i) :=
    μ.toSyn.injective (le_antisymm hqle hqge)
  constructor
  · change μ.Monic q
    simpa only [MonomialOrder.Monic, MonomialOrder.leadingCoeff, hdeg] using hqone
  · exact hdeg

end MvPowerSeries
