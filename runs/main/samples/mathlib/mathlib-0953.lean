@[expose] public section

open scoped ENNReal Topology

open Filter

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {s t : Set α}

section IsFiniteMeasure

lemma measurableSet_sigmaFiniteSetWRT' [IsFiniteMeasure ν] :
    MeasurableSet (μ.sigmaFiniteSetWRT' ν) :=
  MeasurableSet.iUnion measurableSet_sigmaFiniteSetGE

end IsFiniteMeasure
end MeasureTheory
end
