namespace OAI

open MeasureTheory ProbabilityTheory

open scoped BigOperators ENNReal NNReal

namespace Problem367

variable {Ω ι : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem integral_signal_mul_weighted_observation (s : Finset ι) (w : ι → ℝ)
    {R : Ω → ℝ} (S B : ι → Ω → ℝ) (hR : MemLp R 2 μ)
    (hS : ∀ i ∈ s, MemLp (S i) 2 μ) (hB : ∀ i ∈ s, MemLp (B i) 2 μ)
    (hind : ∀ i ∈ s, IndepFun R (B i) μ)
    (hzero : ∀ i ∈ s, ∫ ω, B i ω ∂μ = 0) (t : ℝ) :
    (∫ ω, R ω * (∑ i ∈ s, w i * (t * S i ω + B i ω)) ∂μ) =
      t * ∑ i ∈ s, w i * ∫ ω, R ω * S i ω ∂μ := by
  rw [integral_mul_weighted_sum s w (fun i ω => t * S i ω + B i ω) hR
    (fun i hi => ((hS i hi).const_mul t).add (hB i hi)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_signal_mul_observation hR (hS i hi) (hB i hi) (hind i hi) (hzero i hi) t]
  ring

end Problem367
end OAI
