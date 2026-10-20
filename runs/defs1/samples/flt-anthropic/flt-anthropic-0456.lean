namespace P2MW.S_LanglandsTunnell_CubicInduction_mem_span_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

noncomputable section

namespace W5b3G

open NumberField.AdelicLevel Topology

open scoped Pointwise

variable (v : HeightOneSpectrum (𝓞 ℚ))

def cball (r : ℤ) (x : Fv v) : Set (Fv v) := {z : Fv v | Valued.v (z - x) ≤ WithZero.exp r}

end W5b3G
end
end P2MW.S_LanglandsTunnell_CubicInduction_mem_span_of_apply_one_eq_zero_of_forall_apply_antidiagonal2_mul_upperUnipotent2_eq_indicator
