namespace P2MW.S_ModularCurve_exists_exp_eq_of_invariant_ne_zero_isParabolicHom

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane hiding I

open Filter Complex Set Topology

open scoped MatrixGroups Topology Real

namespace ModularCurve

namespace WindingLog

p2m_open

local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet

section Global

variable {Γ : Subgroup SL(2, ℤ)} {Φ : ℂ → ℂ}
  (hΦ : ∀ τ : ℍ, ContDiffAt ℝ 1 Φ τ) (hne : ∀ τ : ℍ, Φ τ ≠ 0)
  (L₀ : C(ℍ, ℂ)) (hL₀ : ∀ τ : ℍ, exp (L₀ τ) = Φ τ)

variable (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, Φ ((γ • τ : ℍ) : ℂ) = Φ τ)

include hL₀ hinv in
theorem exists_int_coboundary (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) :
    ∃ k : ℤ, ∀ τ : ℍ, L₀ (γ • τ) - L₀ τ = 2 * π * Complex.I * k := by
  have h1 : exp (L₀ (γ • UpperHalfPlane.I) - L₀ UpperHalfPlane.I) = 1 := by
    rw [Complex.exp_sub, hL₀, hL₀, hinv γ hγ, div_self (hL₀ _ ▸ Complex.exp_ne_zero _)]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h1
  refine ⟨k, fun τ => ?_⟩
  rw [coboundary_const L₀ hL₀ hinv γ hγ τ UpperHalfPlane.I, hk]
  ring

end Global
end WindingLog
end ModularCurve
end
end P2MW.S_ModularCurve_exists_exp_eq_of_invariant_ne_zero_isParabolicHom
