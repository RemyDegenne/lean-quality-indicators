namespace P2MW.S_ModularCurve_qExpansion_coeff_comp_smul_mem_adjoin_exp_of_gamma1_mul

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function

open scoped Real Manifold MatrixGroups ModularForm Topology

namespace ALRatFun

variable (N : ℕ)

section Fricke

variable (N : ℕ) [NeZero N]

local notation "Δ" => ModularForm.discriminant

variable {N}

variable (σ : (kN N) ≃ₐ[ℚ] (kN N)) {s : ℕ} (hs : s.Coprime N) (hσ : σ (zetaK N) = zetaK N ^ s)

variable (N) in

def evφ (φ : kN N →+* ℂ) (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (R : MvPolynomial (Idx N) (kN N)) :
    ℍ → ℂ :=
  MvPolynomial.aeval (gen N t) (MvPolynomial.map φ R)

end Fricke
end ALRatFun
end
end P2MW.S_ModularCurve_qExpansion_coeff_comp_smul_mem_adjoin_exp_of_gamma1_mul
