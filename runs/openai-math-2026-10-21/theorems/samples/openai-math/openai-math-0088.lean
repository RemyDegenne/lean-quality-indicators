namespace OAI

section

namespace Nagata.W21

open scoped BigOperators

theorem markedThetaProduct_differentiableAt {ι : Type*} [Fintype ι]
    {τ : ℂ} {a : ι → ℂ} {z : ℂ} (hτ : ‖τ‖ < 1) (ha : ∀ i, a i ≠ 0)
    (hz : z ≠ 0) : DifferentiableAt ℂ (markedThetaProduct τ a) z := by
  classical
  exact DifferentiableAt.fun_finsetProd fun i _ ↦
    thetaProduct_scaled_differentiableAt hτ (ha i) hz

end Nagata.W21
end
end OAI
