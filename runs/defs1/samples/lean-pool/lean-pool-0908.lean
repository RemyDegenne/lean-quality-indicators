@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace WordReduction

namespace Pairing

namespace ReductionToken

/-- Type-valued packaging of a marked rotation with one residual dart at its head. -/
structure ResidualConsRotation {n : ℕ}
    (tokens : List (ReductionToken n))
    (dart : SignedDart (Fin n))
    (remainder : List (SignedDart (Fin n))) where
  /-- The `tokenRemainder` declaration. -/
  tokenRemainder : List (ReductionToken n)
  rotated :
    tokens.IsRotated (.residual dart :: tokenRemainder)
  residual_remainder :
    residualDarts tokenRemainder = remainder

end ReductionToken
end Pairing
end WordReduction
end FiniteCyclicPresentation
end LeanEval.Topology.ClassificationOfSurfaces
end
