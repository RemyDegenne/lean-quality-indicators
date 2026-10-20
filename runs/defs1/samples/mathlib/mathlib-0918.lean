@[expose] public section

variable {α β δ ι R : Type*}

namespace MeasureTheory

open Set ENNReal NNReal

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ μ₁ μ₂ μ₃ ν ν' : Measure α} {s t : Set α}

namespace Measure

/-- We say that `μ` is absolutely continuous with respect to `ν`, or that `μ` is dominated by `ν`,
  if `ν(A) = 0` implies that `μ(A) = 0`. -/
def AbsolutelyContinuous {_m0 : MeasurableSpace α} (μ ν : Measure α) : Prop :=
  ∀ ⦃s : Set α⦄, ν s = 0 → μ s = 0

end Measure
end MeasureTheory
end
