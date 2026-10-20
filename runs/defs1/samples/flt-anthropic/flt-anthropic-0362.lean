namespace P2MW.S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function Polynomial

open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

p2m_open

namespace QExpN

def RealL (h : ℝ) (A : LaurentSeries ℂ) (F : ℍ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun m : ℤ => A.coeff m * 𝕢 h (τ : ℂ) ^ m) (F τ)

end QExpN
end ModularCurve
end
end P2MW.S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant
