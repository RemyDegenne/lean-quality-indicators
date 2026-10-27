public section

namespace CFSG.ComponentClassification.J2Cover.External

open Subgroup CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

theorem conj_beta_apply_conj (g q : P) (hq : betaAut q = q) :
    (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹) (g * q * g⁻¹) = g * q * g⁻¹ := by
  simp only [MulAut.mul_apply, ← map_inv, MulAut.conj_apply]
  rw [show g⁻¹ * (g * q * g⁻¹) * g⁻¹⁻¹ = q by group, hq]

end CFSG.ComponentClassification.J2Cover.External
end
