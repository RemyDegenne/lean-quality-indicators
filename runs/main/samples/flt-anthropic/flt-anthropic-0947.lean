namespace P2MW.S_WeierstrassCurve_nonempty_stabilizer_variableChange_mulEquiv_units_rationalEndSubring

set_option autoImplicit false

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

namespace AutEqEndUnits

p2m_open

p2m_open

section OverF

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

local notation "ι" => algebraMap F k

@[scoped simp] theorem bc_CC (x y : k) (a : F) : bc x y (C (C a)) = algebraMap F k a := by simp [bc]

end OverF
end AutEqEndUnits
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_nonempty_stabilizer_variableChange_mulEquiv_units_rationalEndSubring
