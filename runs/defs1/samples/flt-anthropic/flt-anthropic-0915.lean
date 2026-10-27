namespace P2MW.S_LanglandsTunnell_CubicInduction_isHomogeneous_two_and_sum_pderiv_pderiv_eq_zero_sameTwo_xi

set_option autoImplicit false

namespace WsC

namespace S2H

open MvPolynomial

noncomputable section

def Lap (q : R3) : R3 := ∑ i : Fin 3, pderiv i (pderiv i q)

end
end S2H
end WsC
end P2MW.S_LanglandsTunnell_CubicInduction_isHomogeneous_two_and_sum_pderiv_pderiv_eq_zero_sameTwo_xi
