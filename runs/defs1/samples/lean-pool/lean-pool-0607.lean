@[expose] public section

open scoped InnerProductSpace

namespace TauCeti

namespace DavisKahan

open TauCeti.RealComplexification

open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

variable (U V : Submodule ℝ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

variable {U V}

variable (U V)

/-- **The direct rotation of a pair of real closed subspaces**, in arbitrary
dimension: a bounded operator on the real Hilbert space.

Davis--Kahan 1970, Definition 3.1 and Proposition 3.1, over `ℝ`. -/
def directRotationR (hacute : IsUniformlyAcute U V) : E →L[ℝ] E :=
  realPartOperator
    (spectraDirectRotation (complexifySubmodule U) (complexifySubmodule V)
      (isUniformlyAcute_complexifySubmodule U V hacute))

end
end DavisKahan
end TauCeti
end
