@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal NNReal InnerProductSpace

namespace Malliavin

section Growth

open CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

theorem memLp_mderiv_cylinder_expGrowth {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * Real.exp (c * ‖y‖))
    (L : Fin n → StrongDual ℝ W) :
    MemLp (mderiv μ (fun y ↦ f (fun i ↦ L i y))) 2 μ :=
  memLp_mderiv_cylinder_of_dominated μ hf L
    (ψ := fun x ↦ C * Real.exp (c * ((∑ i, ‖L i‖) * ‖x‖))) hfg' (expGrowth_coord_le hC hc L)
    (integrable_expGrowth_sq μ C c _)

end Growth
end Malliavin
end
