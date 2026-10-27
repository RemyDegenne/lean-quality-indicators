@[expose] public section

open TauCeti.DavisKahan.Angle

open TauCeti.DavisKahan.Sylvester

namespace TauCeti

namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open Set

open scoped InnerProductSpace unitInterval

universe v

section SelectedBranchQuarterAcute

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The explicit Lipschitz coefficient supplied by one fixed separating
contour along an affine bounded perturbation path. -/
noncomputable def selectedBranchProjectionLipschitzConstant
    (Γ : PiecewiseC1ClosedContour) (K : H →L[ℂ] H) (delta : ℝ) : ℝ :=
  ‖rieszNormalization‖ *
    (delta⁻¹ ^ 2 * ‖K‖ * Γ.contourLength)

end SelectedBranchQuarterAcute
end DavisKahanExt
end TauCeti
end
