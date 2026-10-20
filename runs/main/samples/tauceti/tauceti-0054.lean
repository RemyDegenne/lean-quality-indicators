public noncomputable section

open Filter Function OnePoint Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

variable {n : ℕ}

theorem localMultiplicity_onePointMap_pow_coe_of_ne_zero (hn : n ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ z ^ n) (z : OnePoint ℂ) = 1 := by
  rw [localMultiplicity_onePointMap_pow_coe, analyticOrderNatAt,
    (analyticAt_id.pow n).analyticOrderAt_sub_eq_one_of_deriv_ne_zero (by simp [hn, hz]),
    ENat.toNat_one]

end TauCeti.RiemannSurface
end
