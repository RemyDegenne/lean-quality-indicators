namespace P2MW.S_Polynomial_abv_coeff_mul_pow_le_of_evalEval_C_add_X_eq_zero

set_option autoImplicit false

open Polynomial

namespace P2MG3b

open Polynomial

theorem mem_span_X_iff {R : Type*} [CommRing R] (f : PowerSeries R) :
    f ∈ Ideal.span ({PowerSeries.X} : Set (PowerSeries R)) ↔ PowerSeries.constantCoeff f = 0 := by
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]

end P2MG3b
end P2MW.S_Polynomial_abv_coeff_mul_pow_le_of_evalEval_C_add_X_eq_zero
