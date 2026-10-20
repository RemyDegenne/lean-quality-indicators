@[expose] public section

noncomputable section

open Filter ENNReal EMetric Set TopologicalSpace Topology

open scoped NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α E F 𝕜 : Type*}

local infixr:25 " →ₛ " => SimpleFunc

variable [NormedAddCommGroup E] [NormedDivisionRing 𝕜]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

@[inherit_doc MeasureTheory.integral]
notation3 "∫ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => integral μ r

@[inherit_doc MeasureTheory.integral]
notation3 "∫ "(...)", "r:60:(scoped f => integral volume f) => r

@[inherit_doc MeasureTheory.integral]
notation3 "∫ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 => integral (Measure.restrict μ s) r

@[inherit_doc MeasureTheory.integral]
notation3 "∫ "(...)" in "s", "r:60:(scoped f => integral (Measure.restrict volume s) f) => r

section Properties

open ContinuousLinearMap MeasureTheory.SimpleFunc

variable [NormedSpace ℝ E]

variable {f : α → E} {m : MeasurableSpace α} {μ : Measure α}

section Basic

variable (α G)

variable {α G}

theorem dist_integral_le_lintegral_edist
    {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
    dist (∫ a, f a ∂μ) (∫ a, g a ∂μ) ≤ (∫⁻ a, edist (f a) (g a) ∂μ).toReal := by
  grw [dist_eq_norm, ← integral_sub hf hg, norm_integral_le_lintegral_norm]
  simp [edist_eq_enorm_sub]

end Basic
end Properties
end MeasureTheory
end
end
