@[expose] public section

namespace MooreBound

open Module

open scoped BigOperators

namespace DegreeDiameter

/-- The `q`-integer `[n]_q = 1 + q + ... + q^(n-1)`. -/
def qInteger (q n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, q ^ i

end DegreeDiameter
end MooreBound
end
