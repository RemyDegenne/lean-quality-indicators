public section

namespace TauCeti

open PathAlgebra

universe u v w

section PathSpan

variable (k : Type w) (Q : Type u) [Semiring k] [Quiver.{v} Q]

/-- The `k`-span of the paths of length at least `n`: the `n`-th step of the length filtration of
the path algebra. -/
noncomputable def pathSpan (n : ℕ) : Submodule k (pathAlgebra k Q) :=
  Submodule.span k (pathAlgebraBasis k Q '' {x : Quiver.TotalPath Q | n ≤ x.2.2.length})

end PathSpan
end TauCeti
end
