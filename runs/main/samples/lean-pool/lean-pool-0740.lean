@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

open Set Filter MeasureTheory Function

open scoped Topology ContDiff BigOperators

namespace NavierStokes.ShapeTransition

theorem vanishingDebtBound_tendsto (n : ℕ) (B K L BG KA T : ℝ) {P : ℝ} (hP : P ≠ 0) :
    Tendsto (fun C : ℝ => vanishingDebtBound n B K L BG KA (separation T C P) C)
      atTop (𝓝 0) := by
  have hp := prefix_bound_tendsto n B K L T P
  have hi := (separation_tendsto T hP).const_mul (idealPrefixCoefficient n BG KA)
  have hs := (separation_fifth_tendsto T hP).const_mul ((5 / 2) * (2 ^ n * KA ^ 2))
  convert! (hp.add hi).add hs using 1
  · funext C
    dsimp only [vanishingDebtBound]
    ring
  · ring_nf

end NavierStokes.ShapeTransition
end
end
