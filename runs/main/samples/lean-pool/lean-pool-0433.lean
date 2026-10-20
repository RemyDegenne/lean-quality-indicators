@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace WordReduction

namespace Pairing

namespace ResidualDecomposition

theorem blocks_ne_nil_of_word_ne_nil {n : ℕ}
    {word : List (SignedDart (Fin n))}
    (decomposition : ResidualDecomposition word)
    (hne : word ≠ []) :
    decomposition.blocks ≠ [] := by
  cases decomposition with
  | done =>
      exact (hne rfl).elim
  | step =>
      simp [blocks]

end ResidualDecomposition
end Pairing
end WordReduction
end FiniteCyclicPresentation
end LeanEval.Topology.ClassificationOfSurfaces
end
