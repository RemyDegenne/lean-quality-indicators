namespace P2MW.S_MvFormalGroup_cartierDual_pow_apply_eq_finsum_coeff_subst_mul_apply_pow

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

universe u v

noncomputable section

open MvPowerSeries

open scoped TensorProduct

namespace P2mFV

section Operators

variable {k : Type u} [CommRing k] {n : ℕ}

theorem coeff_rowX (a b : Fin n →₀ ℕ) (H : MvPowerSeries (Fin n ⊕ Fin n) k) :
    coeff b (rowX a H) = coeff (a.sumElim b) H := rfl

end Operators
end P2mFV
end
end P2MW.S_MvFormalGroup_cartierDual_pow_apply_eq_finsum_coeff_subst_mul_apply_pow
