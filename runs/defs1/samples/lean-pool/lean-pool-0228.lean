@[expose] public section

noncomputable section

namespace EulerPacketCorrectionScalar

open Set

/-- Initial radius, given by `1/(1+8*R+4*M*Rc+Rc)`. -/
def initialRadius (R M Rc : ℝ) : ℝ := 1/(1+8*R+4*M*Rc+Rc)

end EulerPacketCorrectionScalar
end
end
