@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace Bornology Filter

open scoped Topology Interval ENNReal

variable {X Y ε ε' ε'' E F R : Type*} [MeasurableSpace X] [TopologicalSpace X]

variable [MeasurableSpace Y] [TopologicalSpace Y]

variable [TopologicalSpace ε] [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε']
  [TopologicalSpace ε''] [ESeminormedAddMonoid ε'']
  [NormedAddCommGroup E] [NormedAddCommGroup F] {f g : X → ε} {μ ν : Measure X} {s : Set X}

namespace MeasureTheory

section LocallyIntegrableOn

theorem LocallyIntegrableOn.integrableOn_compact_subset [PseudoMetrizableSpace ε]
    (hf : LocallyIntegrableOn f s μ) {t : Set X} (hst : t ⊆ s) (ht : IsCompact t) :
    IntegrableOn f t μ :=
  (hf.mono_set hst).integrableOn_isCompact ht

end LocallyIntegrableOn
end MeasureTheory
end
