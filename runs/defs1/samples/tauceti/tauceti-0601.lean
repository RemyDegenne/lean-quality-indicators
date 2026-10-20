public section

namespace TauCeti.GraphTwistedIndex

universe u

variable (d : GraphTwistedIndex)

variable (R : Type u) [CommRing R]

/-- The graph automorphism of the Serre Lie algebra attached to a graph-twisted index.

It is induced by the pinned permutation of the Bourbaki-numbered nodes. On an untwisted family the
permutation is the identity; on `²Aₙ`, `²Dₙ`, `²E₆`, and `³D₄` it is respectively the chain
reversal, fork exchange, `E₆` involution, or triality. -/
noncomputable def serreGraphAut :
    Matrix.ToLieAlgebra R (Matrix.transpose d.1.dynkinType.cartanMatrix) ≃ₗ⁅R⁆
      Matrix.ToLieAlgebra R (Matrix.transpose d.1.dynkinType.cartanMatrix) :=
  serreDiagramAut R (Matrix.transpose d.1.dynkinType.cartanMatrix)
    d.cartanMatrix_transpose_submatrix_diagramPerm

end TauCeti.GraphTwistedIndex
end
