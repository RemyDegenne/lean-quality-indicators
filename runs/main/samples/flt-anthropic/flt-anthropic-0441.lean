namespace P2MW.S_MvPowerSeries_exists_eq_sum_subst_mul_of_span_quotient_eq_top

set_option autoImplicit false

open MvPowerSeries

namespace SurjApprox

section Low

variable {σ : Type} {R : Type} [CommRing R]

theorem lowVanishing_mul_le (a b : ℕ) : lowVanishing σ R a * lowVanishing σ R b ≤ lowVanishing σ R (a + b) := by
  classical
  rw [Ideal.mul_le]
  intro p hp q hq d hd
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' := congrArg Finsupp.degree (Finset.HasAntidiagonal.mem_antidiagonal.mp hx)
  rw [map_add] at hx'
  by_cases h1 : x.1.degree < a
  · rw [hp x.1 h1, zero_mul]
  · have h2 : x.2.degree < b := by omega
    rw [hq x.2 h2, mul_zero]

end Low
end SurjApprox
end P2MW.S_MvPowerSeries_exists_eq_sum_subst_mul_of_span_quotient_eq_top
