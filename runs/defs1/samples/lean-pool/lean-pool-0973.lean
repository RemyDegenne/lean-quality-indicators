@[expose] public section

namespace BGS.Markoff

open CategoryTheory

open AlgebraicGeometry

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- The Laurent torus open in an affine equation chart. -/
def weightedSplitTraceLaurentCurveSpec (alpha beta : K) (d e : ℕ) : Scheme :=
  Spec (CommRingCat.of (WeightedSplitTraceLaurentCoordinateRing alpha beta d e))

end
end BGS.Markoff
end
