namespace OAI

section

namespace Erdos3.FixedDensity

open Filter Topology

@[simp]
theorem bundleRankwiseEnvelopeError_zero_parameters
    (α μ : ℕ → ℝ) :
    ∀ d n,
      bundleRankwiseEnvelopeError α (fun _ => 0) μ 0 d n = 0 := by
  intro d
  induction d with
  | zero =>
      intro n
      simp
  | succ d ih =>
      intro n
      rw [bundleRankwiseEnvelopeError_succ_order]
      exact bundleRankwiseNextRow_zero_parameters α μ d _ ih n

end Erdos3.FixedDensity
end
end OAI
