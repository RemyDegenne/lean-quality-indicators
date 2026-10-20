public section

open CategoryTheory

open scoped DirectSum

namespace TopRep

universe u v w

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : TopRep.{max v w} R G)

/-- The direct sum of the shifted coinduced resolution. Degree zero is `C(G, X)`. -/
abbrev gradedResolutionModule := ⨁ n : ℕ, (resolutionX X (n + 1)).V

end TopRep
end
