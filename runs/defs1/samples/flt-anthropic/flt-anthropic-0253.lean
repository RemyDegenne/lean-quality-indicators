namespace P2MW.S_ModularCurve_PDPairing_pairZFun_heckeT0_comm

set_option autoImplicit false

open scoped MatrixGroups

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Aux2T1NAT

section Aux1BaseTwo

namespace ModularCurve

namespace PDPairing

namespace BaseTwo

p2m_open

open Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup MulAction

open scoped MatrixGroups

def rep : Fin 3 → SL(2, ℤ) := ![1, S, g₁]

end BaseTwo
end PDPairing
end ModularCurve
end Aux1BaseTwo
end Aux2T1NAT
end P2MW.S_ModularCurve_PDPairing_pairZFun_heckeT0_comm
