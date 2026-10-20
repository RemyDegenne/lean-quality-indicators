@[expose] public section

universe u

namespace TopCat

open CategoryTheory

/-- The `n`-disk is the set of points in ℝⁿ whose norm is at most `1`,
endowed with the subspace topology. -/
noncomputable def disk (n : ℕ) : TopCat.{u} :=
  ↧(ULift <| Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

end TopCat
end
