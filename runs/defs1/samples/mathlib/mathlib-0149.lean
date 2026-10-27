@[expose] public section

noncomputable section

open Complex MeasureTheory Metric Set

open scoped Topology Interval

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A function `f` `IsExactOn` in `U` if it is the complex derivative of a function on `U`.

In complex variable theory, this is also referred to as "having a primitive". -/
def IsExactOn (f : ℂ → E) (U : Set ℂ) : Prop :=
  ∃ g, ∀ z ∈ U, HasDerivAt g (f z) z

end Complex
end
end
