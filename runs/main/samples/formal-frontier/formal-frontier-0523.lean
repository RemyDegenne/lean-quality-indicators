@[expose] public section

open CategoryTheory Convexity

open scoped BigOperators Simplicial

noncomputable section

namespace AlgebraicTopology

open Convexity Convexity.StdSimplex

universe u

theorem singularSubdivisionIterate_succ (X : TopCat.{u}) (n N : ℕ) :
    singularSubdivisionIterate X n (N + 1) =
      (singularSubdivisionIterate X n N).comp (singularSubdivision X n) := rfl

end AlgebraicTopology
end
end
