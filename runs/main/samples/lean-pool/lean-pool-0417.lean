@[expose] public section

namespace TauCeti

namespace DavisKahan

namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

namespace SameApproximationSingularSequence

theorem prefixGauge_eq
    {𝕜 : Type u} [RCLike 𝕜]
    {E₁ F₁ E₂ F₂ : Type v}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    (N : SymmetricNormingFunction)
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : SameApproximationSingularSequence A B) (n : ℕ) :
    N.prefixGauge n A = N.prefixGauge n B := by
  unfold SymmetricNormingFunction.prefixGauge
  congr 1
  funext i
  exact h i

end SameApproximationSingularSequence
end ExactSinTheta
end DavisKahan
end TauCeti
end
