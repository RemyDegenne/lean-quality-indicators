namespace P2MW.S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0

set_option autoImplicit false

open scoped MatrixGroups

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

p2m_reactivate

p2m_reactivate

section CoresPrimitive

open MulAction

variable {G : Type*} [Group G] (K : Subgroup G) [Fintype (G ⧸ K)] {R : Type*} [CommRing R]

variable (sec : G ⧸ K → G) (hsec : ∀ q : G ⧸ K, (sec q : G ⧸ K) = q)

def HFun (h' : K → R) (x : Additive K →+ R) (y : Additive G →+ R) (g : G) : R :=
  ∑ q : G ⧸ K, (h' (gam K sec hsec q g) +
    x (Additive.ofMul (gam K sec hsec q g)) * (y (Additive.ofMul (sec (g⁻¹ • q))) + y (Additive.ofMul (sec q))))

end CoresPrimitive
end TD
end PDPairing
end ModularCurve
end P2MW.S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0
