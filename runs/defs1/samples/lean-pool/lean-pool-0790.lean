@[expose] public section

open scoped InnerProductSpace

namespace TauCeti

namespace DavisKahan

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

variable {H' : Type v} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  [CompleteSpace H']

/-- Restricted right projection on the generic Halmos summand. -/
noncomputable def genericRightProjection
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosGenericPart U V →L[ℂ] halmosGenericPart U V :=
  restrictToInvariant (V.starProjection) (halmosGenericPart U V)
    (projection_right_reduces_halmosGenericPart U V).1

end
end DavisKahan
end TauCeti
end
