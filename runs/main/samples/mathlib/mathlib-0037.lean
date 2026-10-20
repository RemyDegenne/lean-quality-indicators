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

section Arithmetic

@[to_fun (attr := to_additive (attr := fun_prop))]
protected theorem div [Group β] [IsTopologicalGroup β] (hf : AEStronglyMeasurable[m] f μ)
    (hg : AEStronglyMeasurable[m] g μ) : AEStronglyMeasurable[m] (f / g) μ :=
  ⟨hf.mk f / hg.mk g, hf.stronglyMeasurable_mk.div' hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.div hg.ae_eq_mk⟩

end Arithmetic
end AEStronglyMeasurable
end AEStronglyMeasurable
end MeasureTheory
end
