namespace P2MW.S_LocalNewvector_PSCarrier_finrank_inf_fixedSubmodule_padicK1_of_stable

set_option Elab.async false

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

p2m_reactivate

section DeskModule24

set_option autoImplicit false

noncomputable section

open FLT.PrincipalSeriesGL2Padic FLT.PrincipalSeriesGL2Padic.PSCarrier LocalNewvector LocalNewvector.PSCarrier

namespace P6B

open LocalNewvector

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

open Classical in

noncomputable def shellIdx {M : ℤ} (x : ↥(lowerUnipSubgroup p (-M)) ⧸
    (lowerUnipSubgroup p M).subgroupOf (lowerUnipSubgroup p (-M))) : ℤ :=
  if repCoord p x = 0 then -M else max (-M) (-(repCoord p x).valuation)

end P6B
end
end DeskModule24
end P2MW.S_LocalNewvector_PSCarrier_finrank_inf_fixedSubmodule_padicK1_of_stable
