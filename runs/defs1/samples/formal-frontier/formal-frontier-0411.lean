@[expose] public section

open CategoryTheory Convexity

open scoped BigOperators Simplicial

noncomputable section

namespace Convexity.StdSimplex

/-- The center of an affine simplex, obtained by mapping the domain barycenter
through its affine map; equivalently, the equally weighted average of its vertices. -/
def AffineSimplex.center {m n : ℕ} (a : AffineSimplex m n) :
    StdSimplex ℝ (Fin (m + 1)) :=
  affineMapMk a (barycenter (K := ℝ) (M := Fin (n + 1)))

end Convexity.StdSimplex
end
end
