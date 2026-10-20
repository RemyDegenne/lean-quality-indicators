@[expose] public section

open Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

variable {ι Ω β : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The stopped process of `f` above `r` is the process that is equal to `f` until `leastGE f r`
(the first time `f` passes above `r`), and then is constant afterwards. -/
noncomputable def stoppedAbove [LinearOrder ι] [OrderBot ι] [InfSet ι] [Preorder β]
    (f : ι → Ω → β) (r : β) : ι → Ω → β :=
  stoppedProcess f (leastGE f r)

end MeasureTheory
end
