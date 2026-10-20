namespace P2MW.S_CuspForm_norm_lt_of_heckeTLin_eq_smul

set_option autoImplicit false

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm Filter

open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace AlliAux1HB

namespace Bez

variable {N p : ℕ} (Z : Bez N p)

def r : Option (Fin p) → SL(2, ℤ)
  | none => 1
  | some j => Z.γ₂ * ModularGroup.T ^ ((j : ℕ) : ℤ)

end Bez
end AlliAux1HB
end
end P2MW.S_CuspForm_norm_lt_of_heckeTLin_eq_smul
