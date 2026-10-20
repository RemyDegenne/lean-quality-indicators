namespace P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain

p2m_open

open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

namespace WeierstrassCurve

namespace Affine

namespace CoordinateRing

namespace DetInfra

p2m_open

open IsLocalRing

variable {F : Type*} [Field F] {W : Affine F}

lemma isMaximal_XYIdeal' {x y : F} (h : W.Equation x y) : (XYIdeal W x (C y)).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ <|
    MulEquiv.isField (Field.toIsField F) (quotientXYIdealEquiv (W' := W) h).toMulEquiv

end DetInfra
end CoordinateRing
end Affine
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
