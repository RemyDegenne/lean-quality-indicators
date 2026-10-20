section

@[expose] public section

noncomputable section

namespace NavierStokes.PhysicalResidualJetBounds

open Set Function Filter ProblemStatement WeightedClasses LabelSumBounds

open LocalPhysicalCopyBounds PhysicalWaveSum

open scoped Topology ContDiff BigOperators

theorem clm_apply_jet_bound {D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : D → E →L[ℝ] F} {g : D → E} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : D) {m k : ℕ} (hk : k ≤ m) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfa : ∀ i ≤ m, ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hgb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun y => f y (g y)) x‖ ≤ (2 : ℝ) ^ m * A * B := by
  apply (norm_iteratedFDeriv_clm_apply hf hg x (nat_le_infty k)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfa i ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hk))
          (Nat.cast_nonneg _))
        (hgb (k - i) ((Nat.sub_le _ _).trans hk)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2 : ℝ) ^ k * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ (2 : ℝ) ^ m * A * B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hA) hB

end NavierStokes.PhysicalResidualJetBounds
end
end
end
