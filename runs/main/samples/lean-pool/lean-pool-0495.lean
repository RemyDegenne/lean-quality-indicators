public section

open MeasureTheory Set Filter

open CKN CKN.Foundation.Parabolic

open scoped ENNReal Convolution

noncomputable section

namespace CKN.Leray

theorem integrable_mul_reflect {g κ : Vec3 → ℝ} (hg : MemLp g 2 volume) (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) (x : Vec3) : Integrable fun y => g y * κ (x - y) :=
  hg.integrable_mul (memLp_reflect hκ hκc x)

end CKN.Leray
end
end
