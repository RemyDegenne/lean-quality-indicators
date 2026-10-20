public section

noncomputable section

open MeasureTheory

open scoped ENNReal NNReal

namespace TauCeti

universe u

variable {X : Type u} {p : ℝ≥0∞}

namespace WassersteinComponent

section Basic

variable [MeasurableSpace X] [PseudoEMetricSpace X] {μ₀ : ProbabilityMeasure X}

/-- The probability measure underlying an element of a Wasserstein component. -/
@[coe]
def toProbabilityMeasure (μ : WassersteinComponent p μ₀) : ProbabilityMeasure X := μ.1

end Basic
end WassersteinComponent
end TauCeti
end
end
