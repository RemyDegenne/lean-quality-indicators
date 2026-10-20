namespace P2MW.S_ModularCurve_PDPairing_isFreeGroup_Gamma_four

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

section CuspDefs

variable (Φ : Subgroup SL(2, ℤ))

noncomputable scoped instance [Φ.FiniteIndex] : Fintype (Cusp Φ) := Fintype.ofFinite _

noncomputable def cuspGen (q : Cusp Φ) : Φ :=
  ⟨q.out.out⁻¹ * ModularGroup.T ^ Function.minimalPeriod (ModularGroup.T • ·) q.out * q.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem Φ ModularGroup.T q.out⟩

end CuspDefs
end BaseTwo
end PDPairing
end ModularCurve
end Aux1BaseTwo
end Aux2T1NAT
end P2MW.S_ModularCurve_PDPairing_isFreeGroup_Gamma_four
