namespace OAI

universe u25 u26

section LowerBoundInline

open Set Filter Function

open scoped Topology ContDiff NNReal

open Set Filter Metric

open scoped Topology ContDiff

open Set Filter Function MeasureTheory Metric

open scoped Topology ContDiff NNReal

open Set Filter Function

open scoped Topology ContDiff

open Set Filter Function

open scoped Topology ContDiff NNReal

open Set Filter

open scoped Topology ContDiff

open Set Filter Function

open scoped Topology ContDiff

namespace SmoothODE

variable {E : Type u25} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

theorem fderiv_fiberHomeomorph (f : (ℝ × E) ≃ₜ (ℝ × E)) (T : ℝ)
    (hTime : ∀ z, (f z).1 = z.1 + T) (t : ℝ)
    (hf : ContDiff ℝ ∞ (f : (ℝ × E) → (ℝ × E))) (x a : E) :
    fderiv ℝ (f : (ℝ × E) → (ℝ × E)) (t, x) (0, a) =
      (0, fderiv ℝ (fiberHomeomorph f T hTime t : E → E) x a) := by
  have hi : HasFDerivAt (fun y : E => (t, y)) (ContinuousLinearMap.inr ℝ ℝ E) x := by
    have hh := (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x)
    have he : (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E) =
        ContinuousLinearMap.inr ℝ ℝ E := by
      ext y <;> rfl
    rw [he] at hh
    exact hh
  have hd := (hf.differentiable (by simp) (t, x)).hasFDerivAt.comp x hi
  change HasFDerivAt (fun y : E => f (t, y)) _ x at hd
  have he : (fun y : E => f (t, y)) =
      fun y => (t + T, fiberHomeomorph f T hTime t y) := by
    funext y
    exact Prod.ext (hTime (t, y)) rfl
  have hd' := (hasFDerivAt_const (𝕜 := ℝ) (t + T) x).prodMk
    ((contDiff_fiberHomeomorph f T hTime t hf).differentiable (by simp) x).hasFDerivAt
  have hu := congrArg (fun L : E →L[ℝ] (ℝ × E) => L a)
    ((he ▸ hd).unique hd')
  simpa using hu

end
end SmoothODE
end LowerBoundInline
end OAI
