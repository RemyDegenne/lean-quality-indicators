public section

noncomputable section

open Bundle Manifold

open scoped ContDiff Manifold

namespace TauCeti.SL2Tilde

/-- The lifted hyperbolic reflection, reversing both the horizontal and fibre coordinates
of `SL₂ℝ~`, as an isometry of its Sasaki metric. -/
def reflection : Isom 𝓘(ℝ, ℝ × ℝ × ℝ) SL2Tilde where
  toFun := reflectionFun
  invFun := reflectionFun
  left_inv := reflectionFun_involutive
  right_inv := reflectionFun_involutive
  contMDiff_toFun := contMDiff_reflectionFun
  contMDiff_invFun := contMDiff_reflectionFun
  inner_mfderiv' := inner_mfderiv_reflectionFun

end TauCeti.SL2Tilde
end
end
