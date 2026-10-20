namespace P2MW.S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_pow_of_cuspForm_mul_thetaL_pow_eq_qExpansion

noncomputable section

section Helpers

open UpperHalfPlane ModularForm

open scoped MatrixGroups ModularForm Manifold Topology Pointwise

local notation "Δ" => ModularForm.discriminant

namespace IsIntegralAdjoinCoeffEmbJqInvSol

section Engine

open SlashInvariantForm

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

scoped instance : Fintype (Q Γ) := Fintype.ofFinite _

variable {Γ}

variable {n : ℕ} (G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) ((n : ℤ) * 4))

def Lc (d i m : ℕ) : ℂ :=
  (Lagrange.basis (Finset.range (d + 1)) (fun j : ℕ ↦ (j : ℂ)) i).coeff m

end Engine
end IsIntegralAdjoinCoeffEmbJqInvSol
end Helpers
end
end P2MW.S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_pow_of_cuspForm_mul_thetaL_pow_eq_qExpansion
