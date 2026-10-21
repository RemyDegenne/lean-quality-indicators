namespace OAI

open scoped BigOperators ENNReal NNReal Topology

open Filter

noncomputable section

open Set MeasureTheory

open scoped BigOperators

namespace ThreeState.TreeClauses.Positive

open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Experiment

lemma finite_correlation_sum (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (N : ℕ) (hfixed : Q.probability = finiteProbability Q hl₀ hl₁ N)
    (k : ℕ) (hk : k+1 ≤ N) :
    (∑ j ∈ Finset.range k,
      (3*lam^4*Q.mu^2*((j:ℝ)+1)/(1+(j:ℝ)*(lam^2*Q.mu))-
        lam^4*Q.mu*Q.nu*Real.sqrt ((j:ℝ)+1))) ≤ 3*correlationEntropy Q lam (k+1) := by
  induction k with
  | zero =>
    simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (correlationEntropy_nonneg Q hl₀ hl₁ 1)
  | succ k ih =>
    have hprev := ih (by omega)
    have hi := finite_increment_bound Q hl₀ hl₁ N (k+1) (by omega) (by omega) hfixed
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hi
    rw [Finset.sum_range_succ, correlationEntropy_succ Q hl₀ hl₁ (k+1)]
    linarith

end ThreeState.TreeClauses.Positive
end
end OAI
