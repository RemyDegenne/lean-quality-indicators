@[expose] public section

open scoped Topology

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {γ : ℝ → E} {v : ℝ → E → E} {s s' : Set ℝ} {t₀ : ℝ}

lemma isIntegralCurveAt_iff_exists_pos :
    IsIntegralCurveAt γ v t₀ ↔ ∃ ε > 0, IsIntegralCurveOn γ v (Metric.ball t₀ ε) := by
  rw [IsIntegralCurveAt, Metric.eventually_nhds_iff_ball]
  congrm ∃ ε > 0, ∀ (y : ℝ) (hy : y ∈ Metric.ball t₀ ε), ?_
  exact ⟨HasDerivAt.hasDerivWithinAt, fun h ↦ h.hasDerivAt (Metric.isOpen_ball.mem_nhds hy)⟩

end
