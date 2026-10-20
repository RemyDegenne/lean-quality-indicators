public section

namespace TauCeti

open MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜]

theorem tsum_inner_mul_inner_hermiteFunctionLp (f g : Lp 𝕜 2 (volume : Measure ℝ)) :
    ∑' n : ℕ, inner 𝕜 f (hermiteFunctionLp 𝕜 n) * inner 𝕜 (hermiteFunctionLp 𝕜 n) g
      = inner 𝕜 f g := by
  simpa using (hermiteHilbertBasis 𝕜).tsum_inner_mul_inner f g

end TauCeti
end
