public section

namespace TauCeti

open Finset _root_.Matrix

namespace AffineDynkinType

variable {t : AffineDynkinType}

/-- The generalized Cartan matrix of an affine simply-laced diagram, over `ℝ`. A simply-laced
Cartan matrix is symmetric (`TauCeti.AffineDynkinType.isSymm_cartanMatrix`), so the symmetrizing
diagonal matrix is the identity and this matrix is already the symmetrized bilinear form of the
diagram. -/
noncomputable def realCartanMatrix (t : AffineDynkinType) :
    Matrix (Fin t.nodes) (Fin t.nodes) ℝ :=
  t.cartanMatrix.map ((↑) : ℤ → ℝ)

end AffineDynkinType
end TauCeti
end
