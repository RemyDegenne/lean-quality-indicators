/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FormalPowerSeries.MvPowerSeries.IdealAdicRestricted.Content
import Mathlib.RingTheory.Ideal.Operations

public section

/-!
# Restricted factorization by a selected coefficient

If a coefficient of a restricted series generates the ideal of all its
coefficients, the series factors by that coefficient with a restricted factor
whose selected coefficient is one. The coefficient need not be regular.
-/

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R] [PreValuationRing R]

omit [PreValuationRing R] in
private theorem exists_power_not_mem (I : Ideal R) [IsHausdorff I R]
    {x : R} (hx : x ≠ 0) : ∃ k : ℕ, x ∉ I ^ k := by
  by_contra h
  push Not at h
  apply hx
  apply (IsHausdorff.haus (I := I) (M := R) inferInstance)
  intro n
  apply (SModEq.zero).2
  simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using h n

omit [PreValuationRing R] in
private theorem exists_deep_quotient (I : Ideal R) [IsHausdorff I R]
    (c x : R) (hx : x ≠ 0) (hxc : x ∈ Ideal.span {c}) :
    ∃ (d : ℕ) (y : R), y ∈ I ^ d ∧ c * y = x ∧
      ∀ n : ℕ, x ∈ Ideal.span {c} * I ^ n → n ≤ d := by
  classical
  obtain ⟨k, hk⟩ := exists_power_not_mem I hx
  let depths : Set ℕ := {n | x ∈ Ideal.span {c} * I ^ n}
  have hbounded : depths ⊆ {n : ℕ | n < k} := by
    intro n hn
    by_contra hnk
    have hkn : k ≤ n := Nat.le_of_not_gt hnk
    exact hk ((Ideal.pow_le_pow_right hkn) (Ideal.mul_le_right hn))
  have hfinite : depths.Finite := (Set.finite_lt_nat k).subset hbounded
  let indices := hfinite.toFinset
  have hzero : (0 : ℕ) ∈ indices := by
    apply hfinite.mem_toFinset.mpr
    simpa only [depths, Set.mem_ofPred_eq, pow_zero, Ideal.one_eq_top,
      Ideal.mul_top] using hxc
  have hnonempty : indices.Nonempty := ⟨0, hzero⟩
  let d := indices.max' hnonempty
  have hd : x ∈ Ideal.span {c} * I ^ d :=
    hfinite.mem_toFinset.mp (indices.max'_mem hnonempty)
  obtain ⟨y, hy, hcy⟩ := Ideal.mem_span_singleton_mul.mp hd
  refine ⟨d, y, hy, hcy, ?_⟩
  intro n hn
  exact indices.le_max' n (hfinite.mem_toFinset.mpr hn)

/-- If a given coefficient generates the ideal of all coefficients of a
restricted series over a separated prevaluation ring, it can be factored out
with a restricted quotient normalized at that same index. -/
theorem IsAdicallyRestricted.exists_selected_coeff_factor (I : Ideal R)
    [IsHausdorff I R] (f : MvPowerSeries σ R) (hf : IsAdicallyRestricted I f)
    (j : σ →₀ ℕ)
    (hj : Ideal.span (Set.range (fun m : σ →₀ ℕ => coeff m f)) =
      Ideal.span {coeff j f}) :
    ∃ g : MvPowerSeries σ R,
      IsAdicallyRestricted I g ∧
      f = C (coeff j f) * g ∧ coeff j g = 1 := by
  classical
  let c := coeff j f
  have hcoeff (m : σ →₀ ℕ) : coeff m f ∈ Ideal.span {c} := by
    rw [← hj]
    exact Ideal.subset_span (Set.mem_range_self m)
  by_cases hc : c = 0
  · have hzero (m : σ →₀ ℕ) : coeff m f = 0 := by
      have hm := hcoeff m
      have hspan : Ideal.span {c} = ⊥ := Ideal.span_singleton_eq_bot.mpr hc
      simpa only [hspan, Submodule.mem_bot] using hm
    have hfzero : f = 0 := ext fun m => by simpa using hzero m
    refine ⟨monomial j 1, ?_, ?_, coeff_monomial_same j 1⟩
    · intro n
      apply (Set.finite_singleton j).subset
      intro m hm
      by_contra hne
      have hz : coeff m (monomial j (1 : R)) = 0 := coeff_monomial_ne hne 1
      exact hm (hz ▸ (I ^ n).zero_mem)
    · simp [hfzero]
  · obtain ⟨N, hN⟩ := exists_power_not_mem I hc
    have htotal : I ^ N ≤ Ideal.span {c} ∨ Ideal.span {c} ≤ I ^ N :=
      (PreValuationRing.iff_ideal_total.mp (inferInstance : PreValuationRing R)).total _ _
    have hpower : I ^ N ≤ Ideal.span {c} := by
      rcases htotal with hle | hle
      · exact hle
      · exact (hN (hle (Ideal.mem_span_singleton_self _))).elim
    have hdeep (n : ℕ) : I ^ (N + n) ≤ Ideal.span {c} * I ^ n := by
      rw [pow_add]
      exact Ideal.mul_mono_left hpower
    have hpoint (m : σ →₀ ℕ) :
        ∃ y : R, c * y = coeff m f ∧
          ∀ n : ℕ, coeff m f ∈ I ^ (N + n) → y ∈ I ^ n := by
      by_cases hm : coeff m f = 0
      · refine ⟨0, by simp [hm], ?_⟩
        intro n _
        exact (I ^ n).zero_mem
      · obtain ⟨d, y, hy, hcy, hmax⟩ :=
          exists_deep_quotient I c (coeff m f) hm (hcoeff m)
        refine ⟨y, hcy, ?_⟩
        intro n hn
        exact (Ideal.pow_le_pow_right (hmax n (hdeep n hn))) hy
    choose y hy using hpoint
    let g : MvPowerSeries σ R := fun m => if m = j then 1 else y m
    have hcoeffg (m : σ →₀ ℕ) : coeff m g = if m = j then 1 else y m := rfl
    have hfactor : f = C c * g := by
      apply ext
      intro m
      rw [coeff_C_mul, hcoeffg]
      by_cases hm : m = j
      · subst m
        simp [c]
      · simp only [hm, ↓reduceIte]
        exact (hy m).1.symm
    have hrestricted : IsAdicallyRestricted I g := by
      intro n
      apply ((hf (N + n)).union (Set.finite_singleton j)).subset
      intro m hm
      by_contra hnot
      have hindex : m ≠ j := by
        intro heq
        exact hnot (Or.inr heq)
      have hmem : coeff m f ∈ I ^ (N + n) := by
        by_contra hbad
        exact hnot (Or.inl hbad)
      apply hm
      simp only [hcoeffg, hindex, ↓reduceIte]
      exact (hy m).2 n hmem
    exact ⟨g, hrestricted, hfactor, by simp only [hcoeffg, eq_self, ↓reduceIte]⟩

end MvPowerSeries
