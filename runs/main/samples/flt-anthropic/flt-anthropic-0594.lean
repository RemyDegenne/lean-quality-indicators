namespace P2MW.S_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply

set_option autoImplicit false

open scoped MatrixGroups ModularForm

p2m_open

namespace ModularCurve

namespace DiaFFBody

p2m_open

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem T_mem_GammaH : ModularGroup.T ∈ CohCarrier.GammaH M H :=
  Gamma1_le_GammaH (by rw [Gamma1_mem]; simp [ModularGroup.T])

end DiaFFBody
end ModularCurve
end P2MW.S_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
