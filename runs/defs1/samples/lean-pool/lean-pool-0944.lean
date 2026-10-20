@[expose] public section

open Complex Filter Function MeasureTheory Metric Set

open scoped Real Topology

namespace SCV

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {ι : Type*} [Fintype ι]

/-- The germ at `x` of a function analytic at `x`. -/
def germ {x : E} (f : E → ℂ) (hf : AnalyticAt ℂ f x) : analyticGermRing x := ⟨f, f, hf, rfl⟩

end SCV
end
