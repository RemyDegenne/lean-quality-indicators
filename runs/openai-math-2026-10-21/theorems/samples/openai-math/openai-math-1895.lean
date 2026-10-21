namespace OAI

open scoped BigOperators ENNReal NNReal Topology

open Filter

noncomputable section

open Set MeasureTheory

namespace ThreeState.TreeClauses.Positive

open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Experiment

theorem regular_fixed_uniform (Q : Law) {lam : ℝ} (hl₀ : 0 < lam) (hl₁ : lam < 1)
    (n : ℕ) (hn : 2 ≤ n) (hcrit : (n:ℝ)*lam^2 = 1)
    (hfixed : Q.probability = finiteProbability Q hl₀.le hl₁ n) :
    ∀ᵐ m ∂Q.probability.toMeasure, m.1 = fun _ ↦ 1 := by
  have hzero := regular_fixed_mu_zero Q hl₀ hl₁ n hn hcrit hfixed
  have he : ∀ᵐ m ∂Q.probability.toMeasure, xMoment m = 0 :=
    (integral_eq_zero_iff_of_nonneg xMoment_nonneg (compact_integrable continuous_xMoment)).1 hzero
  exact he.mono (fun _ hm ↦ message_uniform_of_x_zero hm)

end ThreeState.TreeClauses.Positive
end
end OAI
