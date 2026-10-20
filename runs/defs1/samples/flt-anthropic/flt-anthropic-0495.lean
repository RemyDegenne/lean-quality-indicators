namespace P2MW.S_KatzModularForm_exists_toFun_eq_mul_b2_of_weight_two_zmod_two

set_option autoImplicit false

noncomputable section

namespace K2Two

variable {R : Type} [CommRing R]

open WeierstrassCurve

variable (R)

section TwoChart

open WeierstrassCurve

def Ct₂ : WeierstrassCurve.VariableChange Qr where
  u := 1
  r := WS1.a₃
  s := 0
  t := tT

end TwoChart
end K2Two
end
end P2MW.S_KatzModularForm_exists_toFun_eq_mul_b2_of_weight_two_zmod_two
