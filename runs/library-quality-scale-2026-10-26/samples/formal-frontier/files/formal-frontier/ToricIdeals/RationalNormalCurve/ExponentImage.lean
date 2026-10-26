/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import ToricIdeals.RationalNormalCurve

import Mathlib.Algebra.Group.Submonoid.Pointwise

/-!
# Image of the rational-normal-curve exponent map

The columns `(n-i, i)` of `rncExponent n` are natural-valued exponents of total
`n`. A target exponent belongs to its additive image exactly when its total
is divisible by `n`. This concerns exponents alone, with no coefficient ring
or positivity assumption. At `n = 0`, divisibility by zero forces total zero,
so the image consists only of the zero exponent.

## References

* Formal Frontier Agents, `ToricIdeals.RationalNormalCurve`, for the
  parametrization and its additive exponent map.
* Mathlib contributors, especially Antoine Chambert-Loir and María Inés de
  Frutos-Fernández, for `Finsupp.weight`, `Finsupp.degree` and the natural-valued
  degree-fiber API in `Mathlib.Data.Finsupp.Weight`.
-/

namespace ToricIdeals.RationalNormalCurve

open scoped Pointwise

private theorem degree_eq_coordinate_sum (t : Fin 2 →₀ ℕ) :
    t.degree = t 0 + t 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

private theorem exists_coordinateExponent_of_degree_eq (n : ℕ) (t : Fin 2 →₀ ℕ)
    (ht : t.degree = n) : ∃ i : Fin (n + 1), coordinateExponent n i = t := by
  have htotal : t 0 + t 1 = n := (degree_eq_coordinate_sum t).symm.trans ht
  have hsecond : t 1 < n + 1 := by omega
  have hfirst : n - t 1 = t 0 := by omega
  refine ⟨⟨t 1, hsecond⟩, ?_⟩
  ext q
  fin_cases q
  · simpa [coordinateExponent] using hfirst
  · simp [coordinateExponent]

@[expose] public section

/-- A natural-valued target exponent lies in the image of the degree-`n`
rational-normal-curve exponent map exactly when its total is divisible by `n`.
This includes degree zero, whose image is the zero exponent. -/
theorem mem_mrange_rncExponent_iff (n : ℕ) (t : Fin 2 →₀ ℕ) :
    t ∈ AddMonoidHom.mrange (rncExponent n) ↔ n ∣ (t 0 + t 1) := by
  constructor
  · intro ht
    obtain ⟨d, rfl⟩ := AddMonoidHom.mem_mrange.mp ht
    exact ⟨sourceDegree n d, rncExponent_total n d⟩
  · rintro ⟨m, hm⟩
    have hdegree : t.degree = n * m := (degree_eq_coordinate_sum t).trans hm
    by_cases hm0 : m = 0
    · have ht0 : t = 0 := (Finsupp.degree_eq_zero_iff t).mp (by
        simpa only [hm0, mul_zero] using hdegree)
      subst t
      exact (AddMonoidHom.mrange (rncExponent n)).zero_mem
    · have hcolumns : Finsupp.degree (σ := Fin 2) ⁻¹' ({n} : Set ℕ) ⊆
          (AddMonoidHom.mrange (rncExponent n) : Set (Fin 2 →₀ ℕ)) := by
        intro u hu
        have hu_degree : u.degree = n := Set.mem_singleton_iff.mp hu
        obtain ⟨i, rfl⟩ := exists_coordinateExponent_of_degree_eq n u hu_degree
        exact AddMonoidHom.mem_mrange.mpr
          ⟨Finsupp.single i 1, rncExponent_single n i⟩
      -- Repeated set addition allows different columns in the same sum.
      have hmem : t ∈ m • (Finsupp.degree (σ := Fin 2) ⁻¹' ({n} : Set ℕ)) := by
        rw [← Finsupp.degree_preimage_nsmul ({n} : Set ℕ) m hm0]
        change t.degree ∈ m • ({n} : Set ℕ)
        rw [Set.nsmul_singleton, Set.mem_singleton_iff, Nat.nsmul_eq_mul,
          Nat.mul_comm m n]
        exact hdegree
      exact AddSubmonoid.nsmul_subset (n := m) hcolumns hmem

end

end ToricIdeals.RationalNormalCurve
