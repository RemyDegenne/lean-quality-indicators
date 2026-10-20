@[expose] public section

open TauCeti.DavisKahan.Sylvester

namespace TauCeti

namespace DavisKahan

namespace ExactSinTheta

open scoped InnerProductSpace BigOperators ENNReal

noncomputable section

universe v

section Sharpness

theorem sharp52_two_le_sqrt_ten : (2 : ℝ) ≤ Real.sqrt 10 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10), Real.sqrt_nonneg (10 : ℝ)]

end Sharpness
end
end ExactSinTheta
end DavisKahan
end TauCeti
end
