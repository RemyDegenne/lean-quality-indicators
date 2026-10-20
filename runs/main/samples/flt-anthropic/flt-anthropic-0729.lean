namespace P2MW.S_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

namespace W769

open UpperHalfPlane hiding I

open ModularForm CongruenceSubgroup ModularCurve HahnSeries

open scoped MatrixGroups ModularForm

variable (M : ℕ) [NeZero M]

local notation "Γᴳ" => ((CohCarrier.GammaH M ⊥ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

local notation "Γ₁ᴳ" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M}

variable (X : FB M)

section Field

variable (K : Type*) [Field K]

local notation "F̄" => qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)

local notation "ι" => algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))

omit X in
theorem coe_algebraMap (r : K) : ((ι r : F̄) : LaurentSeries K) = algebraMap K (LaurentSeries K) r := rfl

end Field
end W769
end
end P2MW.S_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq
