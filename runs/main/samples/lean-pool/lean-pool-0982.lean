@[expose] public section

noncomputable section PortComputability

open MeasureTheory

open scoped ENNReal

namespace MarkovProcess

section

namespace LifetimePath

variable {α : Type*} [TopologicalSpace α]

theorem measurable_lifetime [MeasurableSpace α] :
    Measurable (lifetime : LifetimePath α → ENNReal) := by
  apply Measurable.of_comap_le
  exact le_sup_left

end LifetimePath
end
end MarkovProcess
end PortComputability
end
