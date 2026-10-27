namespace P2MW.S_LanglandsTunnell_CubicInduction_eval_sum_act_quadric_realise_rot_pderiv_eq_half_eval_realise_lowerOne

set_option autoImplicit false

namespace WsB

namespace C6

open MvPolynomial

noncomputable section

def Dop (c d : Fin 3) (p : R9) : R9 :=
  ∑ i : Fin 3, ∑ j : Fin 3, Vf c d i j * MvPolynomial.pderiv (i, j) p

end
end C6
end WsB
end P2MW.S_LanglandsTunnell_CubicInduction_eval_sum_act_quadric_realise_rot_pderiv_eq_half_eval_realise_lowerOne
