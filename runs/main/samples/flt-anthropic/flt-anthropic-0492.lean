namespace P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified

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

section PhiInvariance

theorem weyl_mul_lowerUnip' (z : ℚ_[p]) : weyl p * lowerUnip p z = borelElem p 1 1 z * weyl p := by
  rw [← weyl_mul_lowerUnip_mul_weyl p z, mul_assoc (weyl p * lowerUnip p z), weyl_mul_weyl, mul_one]

end PhiInvariance
end PrincipalSeriesGL2Padic
end FLT
end
end DeskModule14
end P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_isUnramified
