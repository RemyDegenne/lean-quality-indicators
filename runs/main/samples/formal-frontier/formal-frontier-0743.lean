@[expose] public section

open CategoryTheory Convexity

open scoped BigOperators Simplicial

noncomputable section

namespace AlgebraicTopology

open Convexity Convexity.StdSimplex

universe u

@[simp]
theorem realizeAffineChain_single {X : TopCat.{u}} {n k : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋n⦌) (a : AffineSimplex n k) :
    realizeAffineChain x k (Finsupp.single a 1) =
      Finsupp.single (affinePostcompose x a) 1 := by
  simp [realizeAffineChain]

end AlgebraicTopology
end
end
