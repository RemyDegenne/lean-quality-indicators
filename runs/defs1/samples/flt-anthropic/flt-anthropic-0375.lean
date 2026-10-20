namespace P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball

set_option autoImplicit false

section P2M_Coefficients

open scoped ComplexOrder

open ArithmeticFunction PowerSeries Finset

namespace LandauSiegel

def CoeffNonneg (A : PowerSeries ℂ) : Prop := ∀ k, 0 ≤ coeff k A

end LandauSiegel
end P2M_Coefficients
end P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball
