namespace OAI

section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators ENNReal NNReal Topology

attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge

namespace DilutedSpinGlass

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace KernelTower

variable {Ω X : Type} [Fintype Ω] [MeasurableSpace X]

theorem measurable_backwardLog (L : ℕ) (T : KernelTower Ω L) (m : Fin L → ℝ)
    {f : X → FinitePath Ω L → ℝ} (hf : ∀ a, Measurable (fun x => f x a)) :
    Measurable (fun x => backwardLog L T m (f x)) := by
  induction L with
  | zero => exact hf ()
  | succ L ih =>
    apply FiniteLaw.measurable_logMean
    intro a
    exact ih (T.2 a) (fun j => m j.succ) (fun b => hf (a,b))

end KernelTower
end DilutedSpinGlass
end
end OAI
