@[expose] public section

namespace Bananas

open Utilities

open Utilities.Certificate SubdivisionGraph

open Utilities.Certificate.SubdivisionGraph.Spec

/-- Paper source: `def-inv` (Definition 2.13), the set `Inv_k(τ)`.

The paper's `k`-inversions are `k`-equivalence classes of inversions, where
`(a,b) ∼ (a',b')` iff `a - a' = b - b'` and `a ≡ a' (mod k)`.  Each class has
a unique representative with `0 ≤ a < k`, and this set of representatives is
what is recorded here. -/
def kInversions (k : ℕ) (τ : ℤ → ℤ) : Set (ℤ × ℤ) :=
  { p | p.1 < p.2 ∧ τ p.1 > τ p.2 ∧ 0 ≤ p.1 ∧ p.1 < k }

end Bananas
end
