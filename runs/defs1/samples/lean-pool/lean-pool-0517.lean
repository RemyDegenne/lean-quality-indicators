@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-- Normal of the upper bound on the last, epigraph-height coordinate. -/
def epigraphUpperNormal (d : ℕ) : Fin (d + 1) → ℚ :=
  Fin.snoc 0 1

end BeyondBethe
end
