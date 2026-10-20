@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace P2

@[simp]
theorem retainWord_inverseWord {n : ℕ}
    (word : List (SignedDart (Fin n))) :
    retainWord (inverseWord word) = inverseWord (retainWord word) := by
  simp [retainWord, inverseWord, List.map_map, Function.comp_def]

end P2
end FiniteCyclicPresentation
end ClassificationOfSurfaces
end Topology
end LeanEval
end
