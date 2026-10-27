@[expose] public section

namespace LeanPool.Shannon1948Formalization

noncomputable section

open Filter

open scoped Topology

/-- Entropy-form expression with logarithm base `b`. -/
def entropyBase
    {α : Type} [Fintype α]
    (b : ℝ)
    (p : ProbDist α) : ℝ :=
  -∑ a, p a * Real.logb b (p a)

end
end LeanPool.Shannon1948Formalization
end
