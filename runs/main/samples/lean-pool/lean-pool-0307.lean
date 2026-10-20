@[expose] public section

open TauCeti.DavisKahan.Sylvester

open scoped InnerProductSpace BigOperators

namespace TauCeti

namespace DavisKahan

namespace TanTheta

open ExactSinTheta

open Module (finrank)

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
theorem hasTheorem63DirectedTangentApproximationNumbers_iff_infinite
    (Z V : Submodule ℂ H) [V.HasOrthogonalProjection]
     (tanTheta0 : Z →L[ℂ] H) :
    HasTheorem63DirectedTangentApproximationNumbers Z V tanTheta0 ↔
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 :=
  Iff.rfl

end TanTheta
end DavisKahan
end TauCeti
end
