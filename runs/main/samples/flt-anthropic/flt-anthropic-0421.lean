namespace P2MW.S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal

attribute [-instance] ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped MatrixGroups ModularForm

open UpperHalfPlane Filter Topology

noncomputable section

namespace ModularCurve

namespace ESDescent

p2m_open

section Action

variable {Γ' Γ : Subgroup SL(2, ℤ)} (hle : Γ' ≤ Γ) (hn : (Γ'.subgroupOf Γ).Normal)

include hle hn in
theorem conj_mem' {γ : SL(2, ℤ)} (hγ : γ ∈ Γ') (δ : Γ) : (δ : SL(2, ℤ))⁻¹ * γ * (δ : SL(2, ℤ)) ∈ Γ' := by
  have := conj_mem hle hn hγ δ⁻¹
  simpa using this

end Action
end ESDescent
end ModularCurve
end
end P2MW.S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal
