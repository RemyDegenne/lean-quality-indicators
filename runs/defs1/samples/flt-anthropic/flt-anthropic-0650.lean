namespace P2MW.S_LocalNewvector_PSCarrier_existsUnique_mem_inf_fixedSubmodule_padicK1_one_of_stable

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

section DeskModule14

set_option autoImplicit false

noncomputable section

open Matrix FLT.EKAverage

namespace FLT

namespace PrincipalSeriesGL2Padic

p2m_open

open LocalNewvector

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

p2m_reactivate

namespace PSCarrier

open LocalNewvector.PSCarrier

variable (h₁ : IsUnramified p μ₁) (h₂ : IsUnramified p μ₂)

def combo (a : ℤ) (X Y : ℂ) : PSCarrier p μ₁ μ₂ :=
  X • bumpV p μ₁ μ₂ h₁ h₂ a + Y • phiV p μ₁ μ₂ h₁ h₂ (a - 1)

end PSCarrier
end PrincipalSeriesGL2Padic
end FLT
end
end DeskModule14
end P2MW.S_LocalNewvector_PSCarrier_existsUnique_mem_inf_fixedSubmodule_padicK1_one_of_stable
