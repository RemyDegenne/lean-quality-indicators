public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Topology unitInterval

universe w v u

namespace TauCeti

variable (X : TopCat.{w})

/-- The cylinder pair `(X × I, X × ∂I)`. -/
abbrev cylinderBoundaryPair : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of (X × I)) (cylinderBoundary X)

end TauCeti
end
end
