namespace P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int

set_option autoImplicit false

open UpperHalfPlane hiding I

open Complex Filter Function

open scoped Real Topology MatrixGroups Manifold ModularForm ArithmeticFunction.sigma

noncomputable section

namespace EisensteinSeries

namespace RamanujanSystemInt

p2m_open

local notation "𝕢₁" => Periodic.qParam 1

open Derivative

def B6 : ℍ → ℂ := (3 : ℂ) • D ⇑ModularForm.E₄ - E2 * ⇑ModularForm.E₄ + ⇑ModularForm.E₆

end RamanujanSystemInt
end EisensteinSeries
end
end P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int
