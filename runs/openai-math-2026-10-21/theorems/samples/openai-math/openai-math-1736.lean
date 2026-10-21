namespace OAI

universe u14 u15 u16

section LowerBoundInline

open Set Filter Function

open scoped Topology ContDiff NNReal

open Set Filter Metric

open scoped Topology ContDiff

open Set Filter Function MeasureTheory Metric

open scoped Topology ContDiff NNReal

namespace SmoothODE

open Set Filter Function MeasureTheory Metric

open scoped Topology ContDiff NNReal

variable {E : Type u16} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

omit [CompleteSpace E] [ProperSpace E] in

theorem homeomorph_pow_preserves_tensor_on (f : E ≃ₜ E)
    (hf : ContDiff ℝ ∞ (f : E → E)) {U : Set E} (hU : MapsTo f U U)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ x ∈ U, ∀ a b, B (f x) (fderiv ℝ (f : E → E) x a)
      (fderiv ℝ (f : E → E) x b) = B x a b) (n : ℕ) (x : E) (hx : x ∈ U) :
    (f ^ n) x ∈ U ∧ ∀ a b,
      B ((f ^ n) x) (fderiv ℝ ((f ^ n : E ≃ₜ E) : E → E) x a)
        (fderiv ℝ ((f ^ n : E ≃ₜ E) : E → E) x b) = B x a b := by
  induction n with
  | zero =>
    refine ⟨hx, ?_⟩
    intro a b
    change B x (fderiv ℝ (id : E → E) x a) (fderiv ℝ (id : E → E) x b) = _
    simp
  | succ n ih =>
    rw [pow_succ']
    refine ⟨hU ih.1, ?_⟩
    intro a b
    change B (f ((f ^ n) x)) (fderiv ℝ ((f : E → E) ∘ (f ^ n : E ≃ₜ E)) x a)
      (fderiv ℝ ((f : E → E) ∘ (f ^ n : E ≃ₜ E)) x b) = _
    rw [fderiv_comp x (hf.differentiable (by simp) _)
      ((contDiff_homeomorph_pow f hf n).differentiable (by simp) _)]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hB _ ih.1]
    exact ih.2 a b

end
end SmoothODE
end LowerBoundInline
end OAI
