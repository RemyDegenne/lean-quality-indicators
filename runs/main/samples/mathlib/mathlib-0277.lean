@[expose] public section

noncomputable section

open Filter Set Filter Real

open scoped Topology

namespace Real

variable {x y : ℝ}

theorem lt_arcsin_iff_sin_lt' {x y : ℝ} (hx : x ∈ Ico (-(π / 2)) (π / 2)) :
    x < arcsin y ↔ sin x < y :=
  not_le.symm.trans <| (not_congr <| arcsin_le_iff_le_sin' hx).trans not_le

end Real
end
end
