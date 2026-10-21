namespace OAI

namespace Falconer

open Set Metric MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {d h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_direction_pruning_incidence_cost
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {δ : ℝ} (hδ : 0 < δ) (r : ι → ℝ) (T C : ι → ℝ≥0∞) (hT : ∀ i, 0 < T i)
    (hp : ∀ i, (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows d h) ≤ C i) :
    (∫⁻ p : (Fin h → Space d) × Space h, gaussianPointMass μ δ p*
      gaussianDirectionSliceMeasure ν p.1 δ
        (finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r T)ᶜ
        ∂(gaussianRows d h).prod volume) ≤
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (T i)⁻¹*C i) := by
  rw [gaussian_point_weighted_label_integral μ hδ _
    (gaussian_direction_good_compl_mass_measurable ν δ r T)]
  exact mul_le_mul_right (gaussian_direction_finite_ball_deletion ν δ r T C hT hp) _

end Falconer
end OAI
