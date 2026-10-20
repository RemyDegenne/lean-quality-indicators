namespace P2MW.S_ModularCurve_PhiGen_sum_qTwist_coeff

set_option autoImplicit false

noncomputable section

p2m_open

open scoped IntermediateField

namespace ModularCurve

namespace W1

p2m_open

variable {K : Type*} [Field K] [Algebra ℚ K]

theorem iota_jq (N : ℕ) [NeZero N] : coeffEmb K (qExpand ℚ N jq) = TS K N 1 := by
  rw [coeffEmb_qExpand, TS, qTwist_one_apply]

end W1
end ModularCurve
end
end P2MW.S_ModularCurve_PhiGen_sum_qTwist_coeff
