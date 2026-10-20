namespace P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball

set_option autoImplicit false

p2m_reactivate

p2m_reactivate

p2m_reactivate

section P2M_SiegelFunction

p2m_open

namespace LandauSiegel

noncomputable def zeta0 (s : ℂ) : ℂ :=
  (riemannZeta s - 1 / (s - 1) / Gammaℝ s) + dslope (fun s ↦ (Gammaℝ s)⁻¹) 1 s

end LandauSiegel
end P2M_SiegelFunction
end P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball
