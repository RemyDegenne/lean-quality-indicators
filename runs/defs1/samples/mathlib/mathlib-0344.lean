@[expose] public section

noncomputable section

open scoped MeasureTheory NNReal ENNReal

open Set

variable {α : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}

namespace MeasureTheory

attribute [instance] HaveLebesgueDecomposition.posPart

attribute [instance] HaveLebesgueDecomposition.negPart

namespace ComplexMeasure

/-- A complex measure is said to `HaveLebesgueDecomposition` with respect to a positive measure
if both its real and imaginary part `HaveLebesgueDecomposition` with respect to that measure. -/
class HaveLebesgueDecomposition (c : ComplexMeasure α) (μ : Measure α) : Prop where
  rePart : c.re.HaveLebesgueDecomposition μ
  imPart : c.im.HaveLebesgueDecomposition μ

end ComplexMeasure
end MeasureTheory
end
end
