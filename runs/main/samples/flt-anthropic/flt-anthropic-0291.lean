namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_regularProlongation_mem_integers_iff_of_le

open Polynomial AlgebraicCurve IsLocalRing

namespace CoarsenSol

universe u

section Basic

variable {L : Type*} [Field L] {A A' : ValuationSubring L} (hA : A ≤ A')

variable {F : Type u} [Field F] [Algebra L F]

variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

variable (R : RegularProlongation A F Fb)

theorem algebraMap_mem_O'_iff (x : L) : algebraMap L F x ∈ O' hA R ↔ x ∈ A' := by
  constructor
  · rintro ⟨a, ha, hax⟩
    rw [Algebra.smul_def, ← map_mul, R.algebraMap_mem_iff] at hax
    have ha0 := ne_zero_of_valuation_eq_one ha
    have : x = a⁻¹ * (a * x) := by rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
    rw [this]
    exact mul_mem (mem_of_valuation_eq_one (valuation_inv_eq_one ha)) (hA hax)
  · intro hx
    by_cases hxA : x ∈ A
    · exact le_O' hA R (algebraMap_mem R hxA)
    ·
      have hx1 : A'.valuation x = 1 := by
        rcases (A'.valuation_le_one_iff x).mpr hx |>.lt_or_eq with h | h
        · exact absurd (mem_A_of_valuation_lt_one hA h) hxA
        · exact h
      have hx0 := ne_zero_of_valuation_eq_one hx1
      refine ⟨x⁻¹, valuation_inv_eq_one hx1, ?_⟩
      rw [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hx0, map_one]
      exact one_mem _

end Basic
end CoarsenSol
end P2MW.S_AlgebraicCurve_RegularProlongation_exists_regularProlongation_mem_integers_iff_of_le
