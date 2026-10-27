namespace P2MW.S_ModularCurve_integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

noncomputable section

open UpperHalfPlane hiding I

open Filter Complex MeasureTheory Asymptotics

open scoped MatrixGroups Topology ModularForm ComplexConjugate Real NNReal Pointwise

namespace ModularCurve

namespace GreenSidePairing

p2m_open

variable {Γ : Subgroup SL(2, ℤ)}

section Tile

variable [Γ.FiniteIndex] (g : CuspForm Γ 2) (L : ℂ → ℂ) (L' : ℂ → ℂ →L[ℝ] ℂ)
  (hL : ∀ z : ℂ, 0 < z.im → HasFDerivAt L (L' z) z)
  (hL' : ContinuousOn L' {z : ℂ | 0 < z.im}) (σ : SL(2, ℤ))
  (hbd : ∃ C Y : ℝ, ∀ z : ℂ, Y ≤ z.im →
    ‖L ((σ • ofComplex z : ℍ) : ℂ)‖ ≤ C ∧
      ‖fderiv ℝ (fun u : ℂ => L ((σ • ofComplex u : ℍ) : ℂ)) z‖ ≤ C)

def Φt (L : ℂ → ℂ) (g : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ := Lt L σ z * slashC g σ z

end Tile
end GreenSidePairing
end ModularCurve
end
end P2MW.S_ModularCurve_integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing
