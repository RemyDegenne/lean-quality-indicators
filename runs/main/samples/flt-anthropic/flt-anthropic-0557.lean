namespace P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open scoped MatrixGroups

p2m_open

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace FTWcore

open Finset

p2m_reactivate

section WalkSum

variable {W : Type} {𝒯 : SimpleGraph W} {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]

@[scoped simp] theorem dartSum_cons (μ : W → W → ℤ) {u v w : W} (h : 𝒯.Adj u v) (p : 𝒯.Walk v w) :
    dartSum μ (SimpleGraph.Walk.cons h p) = μ u v + dartSum μ p := by
  simp [dartSum]

end WalkSum
end FTWcore
end
end P2MW.S_CerednikDrinfeld_Omega_v_theta_pmoebius_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq
