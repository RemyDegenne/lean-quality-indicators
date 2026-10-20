public section

open Finset

namespace TauCeti

/-- Indices of consecutive pairs of finite heights. No index outside this set
represents a genuine unit edge. -/
def finiteEdges (h : ℕ → WithTop ℝ) : Set ℕ :=
  {n | h n ≠ ⊤ ∧ h (n + 1) ≠ ⊤}

end TauCeti
end
