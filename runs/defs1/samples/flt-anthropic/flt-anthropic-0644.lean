namespace P2MW.S_KatzModularForm_exists_toFun_eq_mul_b2_of_weight_two_zmod_two_pow

set_option autoImplicit false

noncomputable section

namespace KTwoPow

variable {R : Type} [CommRing R]

open WeierstrassCurve

variable (R)

def trCoeffs : Fin 5 → B3 R :=
  ![(C3 R • W3 R).a₁, (C3 R • W3 R).a₂, (C3 R • W3 R).a₃, (C3 R • W3 R).a₄, (C3 R • W3 R).a₆]

end KTwoPow
end
end P2MW.S_KatzModularForm_exists_toFun_eq_mul_b2_of_weight_two_zmod_two_pow
