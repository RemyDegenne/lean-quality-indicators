@[expose] public section

open scoped NNReal Topology

open Set MeasureTheory Measure Filter Function MeasurableSpace ENNReal

variable {α β δ ι : Type*}

namespace MeasureTheory

variable {m0 : MeasurableSpace α} [mβ : MeasurableSpace β] {μ ν ν₁ ν₂ : Measure α}
  {s t : Set α}

namespace Measure

namespace FiniteAtFilter

variable {f g : Filter α}

theorem inf_of_right (h : μ.FiniteAtFilter g) : μ.FiniteAtFilter (f ⊓ g) :=
  h.filter_mono inf_le_right

end FiniteAtFilter
end Measure
end MeasureTheory
end
