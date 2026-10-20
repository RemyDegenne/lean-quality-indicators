namespace P2MW.S_ModularCurve_jqN_sq_not_mem_adjoin

set_option autoImplicit false

noncomputable section

p2m_open

namespace ModularCurve

namespace W1

p2m_open

variable {K : Type*} [Field K] [Algebra ℚ K]

theorem iota_jqN (N d : ℕ) [NeZero N] [NeZero d] :
    coeffEmb K (qExpand ℚ N (jqN d)) = TS K (N * d) 1 := by
  rw [jqN, coeffEmb_qExpand, coeffEmb_qExpand, qExpand_qExpand, TS, qTwist_one_apply]

end W1
end ModularCurve
end
end P2MW.S_ModularCurve_jqN_sq_not_mem_adjoin
