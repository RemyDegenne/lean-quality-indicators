@[expose] public section

open CategoryTheory Convexity

open scoped BigOperators Simplicial

noncomputable section

namespace Convexity.StdSimplex

/-- Finite integer linear combinations of affine `n`-simplices in the standard
`m`-simplex, represented by finitely supported coefficient functions. -/
abbrev AffineChain (m n : ℕ) := AffineSimplex m n →₀ ℤ

end Convexity.StdSimplex
end
end
