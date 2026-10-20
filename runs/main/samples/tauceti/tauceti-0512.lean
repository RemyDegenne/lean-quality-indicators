public section

noncomputable section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Universal.Affine

variable {m n : ℤ}

-- The certificate is `ω_def` at `2`: the reduced-invariant denominator is `1` and the
-- complement's auxiliary term `0`, the multiples of the Weierstrass polynomial vanish,
-- `polynomialY` is `ψ₂` and `C Ψ₃` is `ψ₃`, giving the numerator `addY` produces over `ψ₂³`.
lemma addY_smul_one_smul_one :
    pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2 := by
  have hψ₂ : polyToField (curve.ψ 2) ≠ 0 := polyToField_ψ_ne_zero two_ne_zero
  have hY : Affine.polynomialY curve = curve.ψ 2 := by rw [ψ_two, ψ₂]
  have hneg : Affine.negPolynomial curve
      = -(Y : Poly) - (CC curve.a₁ * C X + CC curve.a₃) := by
    rw [Affine.negPolynomial]
    simp only [C_add, C_mul]
  have hF := congrArg polyToField (ω_def curve 2)
  simp only [reducedInvarDenom_two, complEDS₂Aux_two, one_mul, sub_zero, hY, hneg, ← ψ_three,
    map_add polyToField, map_sub polyToField, map_mul polyToField, map_pow polyToField,
    map_neg polyToField, polyToField_polynomial, mul_zero] at hF
  rw [Affine.addY, Affine.negAddY, addX_smul_one_smul_one, smulY_one, smulX_two, smulX_one,
    slopeOne_eq_neg_div, Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulY_def 2, hF]
  field_simp
  ring

end WeierstrassCurve.Universal.Affine
end
end
