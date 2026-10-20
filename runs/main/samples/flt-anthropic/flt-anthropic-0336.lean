namespace P2MW.S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 6400000

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

p2m_reactivate

section

p2m_reactivate

section

p2m_reactivate

section

noncomputable section

p2m_open

namespace AlgebraicCurve

p2m_reactivate

p2m_reactivate

namespace RationalFunctionField

variable (K : Type*) [Field K]

section PlaceInfty

variable [DecidableEq (RatFunc K)]

theorem ord_placeInfty_eq_zero_of_intDegree_eq_zero {f : RatFunc K} (hf : f ≠ 0)
    (h : f.intDegree = 0) : (placeInfty K).ord f = 0 := by
  rw [(placeInfty K).ord_eq_zero_iff_adicValuation_eq_one hf,
    ← (inftyValuation_isEquiv_adicValuation K).eq_one_iff_eq_one,
    RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hf, h]
  rfl

end PlaceInfty
end RationalFunctionField
end AlgebraicCurve
end
end
end
end
end
end
end
end
end
end
end
end P2MW.S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed
