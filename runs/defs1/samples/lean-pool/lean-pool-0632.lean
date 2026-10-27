@[expose] public section

open TauCeti.DavisKahan.Angle

open TauCeti.DavisKahan.Sylvester

namespace TauCeti

namespace DavisKahan

namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

section Complex

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Theorem62Data

/-- The raw Sylvester unknown `E_0^* F_1`. -/
def sylvesterOverlap
    (P : Theorem62Data (E := E) (F := F) (G := G) (H := H)) :
    G →L[ℂ] F :=
  P.data.X.adjoint ∘L P.data.F₁

end Theorem62Data
end Complex
end
end ExactSinTheta
end DavisKahan
end TauCeti
end
