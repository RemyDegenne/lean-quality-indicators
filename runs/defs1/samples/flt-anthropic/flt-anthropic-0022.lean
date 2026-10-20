namespace P2MW.S_LanglandsTunnell_ExplicitLift_trace_det_eq_of_agreeUpToPartner_of_conjPow

set_option autoImplicit false

namespace P2mOctCompare

open FLT.ExplicitLift LanglandsTunnell.Lift48 Matrix

def Hex (k : Mat) : Prop := det2 k = 1 ∧ (tr2 k = 1 ∨ tr2 k = -1)

end P2mOctCompare
end P2MW.S_LanglandsTunnell_ExplicitLift_trace_det_eq_of_agreeUpToPartner_of_conjPow
