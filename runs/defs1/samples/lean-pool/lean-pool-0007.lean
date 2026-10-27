@[expose] public section

namespace TauCeti

namespace DavisKahan

open scoped InnerProductSpace

open TauCeti.DavisKahan

open TauCeti.RealComplexification

open TauCeti.DavisKahan.Foundation.RealComplexification

open TauCeti.DavisKahan.ExactSinTheta.ComplexificationApproximation

universe u v

section Generic

variable {𝕜 : Type*} [RCLike 𝕜]

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- The unperturbed lower compression `(α + δ) - A₀`, extended by zero off `P`.

The shift constant is `α + δ`, not `α`: the lower clause is the image of the
upper one under `A ↦ -A`, `α ↦ -(α + δ)`, which is the reflection exchanging the
two sides of the printed gap. -/
noncomputable def lowerBlockShift (A : H →L[𝕜] H) (P : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] (alpha delta : ℝ) : H →L[𝕜] H :=
  P.starProjection ∘L
    (((alpha + delta : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 H - A) ∘L P.starProjection

end Generic
end DavisKahan
end TauCeti
end
