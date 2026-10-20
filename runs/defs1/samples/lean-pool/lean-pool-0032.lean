@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace WordReduction

namespace Pairing

/-- A completed handle at the head of a protected residual-pair interval. -/
structure MarkedHandleBlockCommute {n : ℕ}
    (tokens : List (ReductionToken n)) where
  /-- The `outer` declaration. -/
  outer : Fin n
  /-- The `first` declaration. -/
  first : Fin n
  /-- The `second` declaration. -/
  second : Fin n
  /-- The `outerNegative` declaration. -/
  outerNegative : Bool
  /-- The `insideTokens` declaration. -/
  insideTokens : List (ReductionToken n)
  /-- The `outsideTokens` declaration. -/
  outsideTokens : List (ReductionToken n)
  rotated :
    tokens.IsRotated
      (.residual (dart outer outerNegative) ::
        .completed (.handle first second) ::
        insideTokens ++
        .residual (dart outer (!outerNegative)) ::
        outsideTokens)
  first_ne_second : first ≠ second
  first_ne_outer : first ≠ outer
  second_ne_outer : second ≠ outer
  first_not_mem_inside :
    first ∉
      (ReductionToken.expand insideTokens).map edgeOfDart
  first_not_mem_outside :
    first ∉
      (ReductionToken.expand outsideTokens).map edgeOfDart
  second_not_mem_inside :
    second ∉
      (ReductionToken.expand insideTokens).map edgeOfDart
  second_not_mem_outside :
    second ∉
      (ReductionToken.expand outsideTokens).map edgeOfDart
  outer_not_mem_inside :
    outer ∉
      (ReductionToken.expand insideTokens).map edgeOfDart
  outer_not_mem_outside :
    outer ∉
      (ReductionToken.expand outsideTokens).map edgeOfDart

end Pairing
end WordReduction
end FiniteCyclicPresentation
end LeanEval.Topology.ClassificationOfSurfaces
end
