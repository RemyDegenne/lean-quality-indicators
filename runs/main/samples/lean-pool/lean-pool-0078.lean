section

section

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set Real EulerSmoothLimit EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerVolterraConvolution EulerContinuousTimeIntegral

namespace Evolution

variable {T : ℝ} {hT : 0 ≤ T} (U : Evolution T hT)

variable (C : ℝ) (hC : 0 ≤ C) (W : C(Icc (0 : ℝ) T, ℝ))
  (hW : ∀ t, 0 ≤ W t)
  (hlog : ∀ t, U.gradientNormPath t ≤
    C * (1 + ‖(U.velocity t).toLp‖ + W t * log (exp 1 + tensorNorm 3 (U.velocity t))))

include hC hW hlog

theorem gradient_logarithmic_envelope (t : Icc (0 : ℝ) T) :
    U.gradientNormPath t ≤ logarithmicGronwallConstant C (U.velocity ⟨0,le_rfl,hT⟩) *
      (1+W t)*(1+U.gradientIntegral t) := by
  let b := 1+‖(U.velocity ⟨0,le_rfl,hT⟩).toLp‖
  let e := logEnergyBase (U.velocity ⟨0,le_rfl,hT⟩)
  let d := b+e+gradientEnergyConstant
  let z := 1+U.gradientIntegral t
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have he : 0 ≤ e := (logEnergyBase_pos _).le
  have hk := gradientEnergyConstant_nonneg
  have hg := U.gradientIntegral_nonneg t
  have hd : 0 ≤ d := add_nonneg (add_nonneg hb he) hk
  have hbd : b ≤ d := by dsimp only [d]; linarith only [hT, he, hk]
  have hed : e ≤ d := by dsimp only [d]; linarith only [hT, hb, hk]
  have hkd : gradientEnergyConstant ≤ d := by dsimp only [d]; linarith only [hT, hb, he]
  have hz : 1 ≤ z := by dsimp only [z]; linarith only [hT, hg]
  have hbz : b ≤ d*z := hbd.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz hd)
  have hez : e+gradientEnergyConstant*U.gradientIntegral t ≤ d*z := by
    calc
      _ ≤ d+d*U.gradientIntegral t := add_le_add hed (mul_le_mul_of_nonneg_right hkd hg)
      _ = _ := by dsimp only [z]; ring
  have hfirst : U.gradientNormPath t ≤ C*(b+W t*(e+gradientEnergyConstant*U.gradientIntegral t)) :=
      by
    have h := hlog t
    rw [U.velocity_norm_conserved t] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (U.logarithmic_h3_bound t) (hW t))) hC)
  apply hfirst.trans
  change C*(b+W t*(e+gradientEnergyConstant*U.gradientIntegral t)) ≤ C*d*(1+W t)*z
  calc
    _ ≤ C*(d*z+W t*(d*z)) :=
      mul_le_mul_of_nonneg_left (add_le_add hbz (mul_le_mul_of_nonneg_left hez (hW t))) hC
    _ = _ := by ring

end Evolution
end EulerOrdinarySobolev
end
end
end
end
