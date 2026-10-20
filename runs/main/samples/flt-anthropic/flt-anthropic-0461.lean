set_option autoImplicit false

open scoped NNReal

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem map_yfun (σ : K →+* K) (w : K) : σ (yfun w) = yfun (σ w) := by
  simp only [yfun, map_div₀, map_pow, map_sub, map_one]

end TateCurve
