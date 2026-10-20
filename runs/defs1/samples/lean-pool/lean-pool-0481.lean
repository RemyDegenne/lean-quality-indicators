@[expose] public section

noncomputable section PortComputability

open MeasureTheory Set

namespace MarkovProcess

section

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- The event that a continuous path meets `F` at or before time `t`. -/
def hitsSetBy (t : NNReal) (F : Set alpha) : Set (ContinuousPath alpha) :=
  {omega | ∃ s : Set.Iic t, omega s ∈ F}

end ContinuousPath
end
end MarkovProcess
end PortComputability
end
