namespace P2MW.S_ModularForm_E4_mul_eta_pow_eight_eq

attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option autoImplicit false

p2m_open

namespace ModularCurve

p2m_open

namespace ARails

open Complex

open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

def etaL (N : ℕ) : List ℤ := ((List.range N).map fun n => facL N (n + 1)).foldr (mulL N) (oneL N)

end ARails
end ModularCurve
end P2MW.S_ModularForm_E4_mul_eta_pow_eight_eq
