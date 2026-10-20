@[expose] public section

namespace TauCeti

namespace DavisKahanExt

open scoped InnerProductSpace

open Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]

variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- The bounded off-diagonal coupling on the Hilbert direct sum. -/
noncomputable def unboundedOffDiagonalCoupling
    (B01 : E1 →L[𝕜] E0) (B10 : E0 →L[𝕜] E1) :
    WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1) :=
  ((WithLp.prodContinuousLinearEquiv 2 𝕜 E0 E1).symm :
      (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1)) ∘L
    ((B01 ∘L WithLp.sndL 2 𝕜 E0 E1).prod
      (B10 ∘L WithLp.fstL 2 𝕜 E0 E1))

end DavisKahanExt
end TauCeti
end
