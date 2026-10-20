@[expose] public section

open Filter Order TopologicalSpace WithTop

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω β ι : Type*} {m : MeasurableSpace Ω}

section MeasurableSet

section CountableStoppingTime

namespace IsStoppingTime

variable [PartialOrder ι] {τ : Ω → WithTop ι} {f : Filtration ι m}

protected theorem measurableSet_lt_of_countable [Countable ι] (hτ : IsStoppingTime f τ) (i : ι) :
    MeasurableSet[f i] {ω | τ ω < i} :=
  hτ.measurableSet_lt_of_countable_range (Set.to_countable _) i

end IsStoppingTime
end CountableStoppingTime
end MeasurableSet
end MeasureTheory
end
