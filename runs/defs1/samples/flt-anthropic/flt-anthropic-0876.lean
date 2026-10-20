namespace P2MW.S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0

set_option autoImplicit false

open scoped MatrixGroups

p2m_reactivate

p2m_reactivate

section Aux2CuspTower

set_option autoImplicit false

open MulAction Function

noncomputable section

namespace ModularCurve

namespace PDPairing

namespace CuspTower

p2m_open

variable {G : Type*} [Group G] (g : G) (K' K : Subgroup G)

variable {K' K}

def towerLift (hle : K' ≤ K) (q : ACusp g K) (o : InnerOrbit g K' K hle q) : G :=
  (q.out.out : G) * ((o.out.out : K) : G)

end CuspTower
end PDPairing
end ModularCurve
end
end Aux2CuspTower
end P2MW.S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0
