namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_read_lowerTwo_xi_of_read_signIsotypic

set_option autoImplicit false

namespace WsB

namespace C6

open MvPolynomial

noncomputable section

def lower2 (M : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ)) : MvPolynomial (Fin 3) ℂ :=
  ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))

end
end C6
end WsB
end P2MW.S_LanglandsTunnell_CubicInduction_exists_read_lowerTwo_xi_of_read_signIsotypic
