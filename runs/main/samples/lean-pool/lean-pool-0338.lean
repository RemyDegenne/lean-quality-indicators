@[expose] public section

noncomputable section

namespace NavierStokes.RadialPullback

open Set Filter MeasureTheory

open scoped Topology ContDiff BigOperators

open WeightedRadialPrimitive

section Sources

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem pullback_contDiff {a : ℝ} (ha : 0 < a) (d : ℝ)
    {F : ℝ × E → V} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (pullback d a F) :=
  hF.comp (liftChart_contDiff (powerChart_contDiff ha d))

end Sources
end NavierStokes.RadialPullback
end
end
