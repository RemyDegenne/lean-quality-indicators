@[expose] public section

open Topology Unitary

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

namespace IsHermitian

variable (hA : IsHermitian A)

/-- The continuous functional calculus of a Hermitian matrix as a triple product using the
spectral theorem. Note that this actually operates on bare functions since every function is
continuous on the spectrum of a matrix, since the spectrum is finite. This is shown to be equal to
the generic continuous functional calculus API in `Matrix.IsHermitian.cfc_eq`. In general, users
should prefer the generic API, especially because it will make rewriting easier. -/
protected noncomputable def cfc (f : ℝ → ℝ) : Matrix n n 𝕜 :=
  conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues))

end IsHermitian
end Matrix
end
