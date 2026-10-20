public section

open Filter ENNReal

open scoped Topology

namespace MeasureTheory

section Bilinear

variable {α E F G ε ε' ε'' : Type*} {m : MeasurableSpace α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [TopologicalSpace ε] [ENormedAddMonoid ε] [TopologicalSpace ε'] [ENormedAddMonoid ε']
  [TopologicalSpace ε''] [ENormedAddMonoid ε'']
  {μ : Measure α} {f : α → E} {g : α → F}

open NNReal

theorem eLpNorm_le_eLpNorm_mul_eLpNorm_top (p : ℝ≥0∞) (b : E → F → G) (c : ℝ≥0)
    (hb : Continuous b.uncurry)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ c * ‖f x‖₊ * ‖g x‖₊) :
    eLpNorm (fun x => b (f x) (g x)) p μ ≤ c * eLpNorm f p μ * eLpNorm g ∞ μ :=
  eLpNorm_le_eLpNorm_mul_eLpNorm_top_of_enorm p b c hb.comp_aestronglyMeasurable₂ hg
    (ae_enorm_bilin_le_of_ae_nnnorm_le h)

end Bilinear
end MeasureTheory
end
