@[expose] public section

open MeasureTheory

open ProbabilityTheory

open scoped ENNReal

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

theorem coeFn_kernelLpTop (μ : Measure α) (κ : Kernel α α)
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ) (f : Lp ℝ ∞ μ) :
    kernelLpTop μ κ hκ hκμ f =ᵐ[μ] kernelIntegral κ f := by
  rw [kernelLpTop, LinearMap.mkContinuous_apply]
  exact MemLp.coeFn_toLp (MemLp.kernelIntegral_top hκ hκμ (Lp.memLp f))

end MarkovProcess
end
