@[expose] public section

open CategoryTheory Convexity

open scoped BigOperators Simplicial

noncomputable section

namespace Convexity.StdSimplex

theorem homotopySimplex_succ {m n : ℕ} (a : AffineSimplex m (n + 1)) :
    homotopySimplex (n + 1) a =
      affineCone m (n + 1) a.center
        (Finsupp.single a 1 - subdivideSimplex (n + 1) a -
          affineHomotopy m n (affineBoundaryGenerator a)) := by
  simp only [homotopySimplex, affineBoundaryGenerator]
  rw [map_sum]
  simp only [map_smul, affineHomotopy_single]

end Convexity.StdSimplex
end
end
