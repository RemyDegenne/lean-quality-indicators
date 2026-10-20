@[expose] public section

namespace LeanPool.CencovPetz

open scoped BigOperators

universe u

namespace MarkovMorphism

variable {α : Type u} [Fintype α]

/-- The target type for a fiberwise split: `Σ a, Fin (m a)`. -/
abbrev SplitTarget (m : α → ℕ) : Type u :=
  Sigma fun a : α => Fin (m a)

end MarkovMorphism
end LeanPool.CencovPetz
end
