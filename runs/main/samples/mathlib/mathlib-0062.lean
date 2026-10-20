@[expose] public section

open MeasureTheory Filter TopologicalSpace Function Set MeasureTheory.Measure

open ENNReal Topology MeasureTheory NNReal

variable {α β γ ι : Type*} [Countable ι]

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

section AEStronglyMeasurable

variable [TopologicalSpace β] [TopologicalSpace γ] {m m₀ : MeasurableSpace α} {μ ν : Measure[m₀] α}
  {f g : α → β}

namespace AEStronglyMeasurable

@[fun_prop]
protected theorem real_toNNReal {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (f x).toNNReal) μ :=
  continuous_real_toNNReal.comp_aestronglyMeasurable hf

end AEStronglyMeasurable
end AEStronglyMeasurable
end MeasureTheory
end
