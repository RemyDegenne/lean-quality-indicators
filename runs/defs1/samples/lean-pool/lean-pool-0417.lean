@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace HandleToCrosscaps

/-- The result of rewriting the two negative occurrences of `b`. -/
@[reducible]
def afterSecond {n : ℕ} (a b c : Fin n)
    (X Y : List (SignedDart (Fin n))) :
    FiniteCyclicPresentation :=
  Crosscap.negativeTarget b
    ([.neg c] ++ Y ++ [.pos a] ++ [.neg c])
    (inverseWord X ++ [.pos a])

end HandleToCrosscaps
end FiniteCyclicPresentation
end LeanEval.Topology.ClassificationOfSurfaces
end
