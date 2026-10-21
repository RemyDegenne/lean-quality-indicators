namespace OAI

namespace BFSSRellich

noncomputable section

open MeasureTheory Set

open scoped ENNReal NNReal BoundedContinuousFunction

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

variable {ι : Type*} [Fintype ι]

omit [CompleteSpace F] in
lemma kernelAverage_bound {κ : Euclidean (ι := ι) → ℝ}
    (hκ : Continuous κ) {C : ℝ} (hC : ∀ x, ‖κ x‖ ≤ C)
    {f : Euclidean (ι := ι) → F} (hf : Integrable f volume) (x : Euclidean (ι := ι)) :
    ‖kernelAverage κ f x‖ ≤ C * ∫ y, ‖f y‖ := by
  calc
    _ ≤ ∫ y, ‖κ (y - x) • f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, C * ‖f y‖ := by
      apply integral_mono (kernel_integrable hκ hC hf x).norm (hf.norm.const_mul C)
      intro y
      change ‖κ (y - x) • f y‖ ≤ C * ‖f y‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hC (y - x)) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

end
end BFSSRellich
end OAI
