public section

noncomputable section

open Filter Set Topology

open scoped ENNReal NNReal

namespace TauCeti

section EMetricSpace

variable {X : Type*} [EMetricSpace X] {φ : X → EReal} {x : X}

theorem descendingSlope_const_mul {c : ℝ} (hc : 0 ≤ c) (f : X → ℝ) (x : X) :
    descendingSlope (fun y ↦ ((c * f y : ℝ) : EReal)) x =
      ENNReal.ofReal c * descendingSlope (fun y ↦ (f y : EReal)) x := by
  rw [descendingSlope_coe, descendingSlope_coe,
    ← ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  congr 1 with y
  rw [← mul_sub, ENNReal.ofReal_mul hc, mul_div_assoc]

end EMetricSpace
end TauCeti
end
end
