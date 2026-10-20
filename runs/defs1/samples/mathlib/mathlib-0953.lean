@[expose] public section

open scoped ENNReal NNReal Topology

open Set MeasureTheory Measure Filter MeasurableSpace ENNReal Function

variable {R α β δ ι : Type*}

namespace MeasureTheory

variable {m0 : MeasurableSpace α} [MeasurableSpace β]

variable {μ ν : Measure α} {s s' t : Set α}

namespace Measure

/-- Restrict a measure `μ` to a set `s`. -/
noncomputable def restrict {_m0 : MeasurableSpace α} (μ : Measure α) (s : Set α) : Measure α :=
  restrictₗ s μ

end Measure
end MeasureTheory
end
