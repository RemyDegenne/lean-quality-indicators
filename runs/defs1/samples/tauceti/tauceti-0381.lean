public section

open scoped ENNReal NNReal

universe u v w

namespace TauCeti

namespace OperatorIdealFamily

/-- The Schatten `p` operator-ideal family, induced by the ℓᵖ symmetric gauge. -/
noncomputable def schatten (𝕜 : Type u) [RCLike 𝕜] (p : ℝ) (hp : 1 ≤ p) :
    OperatorIdealFamily.{u, v, w} 𝕜 :=
  (SymmetricGauge.lpGauge p hp).operatorIdealFamily 𝕜

end OperatorIdealFamily
end TauCeti
end
