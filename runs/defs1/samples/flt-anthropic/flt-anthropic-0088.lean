namespace P2MW.S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0

set_option autoImplicit false

open scoped MatrixGroups

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace ModularCurve

namespace PDPairing

namespace TD

p2m_open

section GlueA

open CongruenceSubgroup MulAction Function ModularGroup ModularCurve.Sanov ModularCurve.PDPairing.SanPM ModularCurve.PDPairing.SanThree ModularCurve.PDPairing.Schreier

variable {R : Type*} [CommRing R]

variable (Φ : Subgroup SL(2, ℤ))

noncomputable def faceGen (i : Fin 3) : ↥sanovSubgroup := wprod sanL (faceRound i)

end GlueA
end TD
end PDPairing
end ModularCurve
end P2MW.S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0
