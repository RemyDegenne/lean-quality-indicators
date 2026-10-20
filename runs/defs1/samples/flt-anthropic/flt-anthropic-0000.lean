namespace P2MW.S_WeierstrassCurve_natCard_stabilizer_torsionOrbit_bot_eq_two

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace STAB2E100

variable {K : Type*} [Field K] [DecidableEq K]

section transport

variable (E : WeierstrassCurve K)

def negVC : VariableChange K := ⟨-1, 0, -E.a₁, -E.a₃⟩

end transport
end STAB2E100
end P2MW.S_WeierstrassCurve_natCard_stabilizer_torsionOrbit_bot_eq_two
