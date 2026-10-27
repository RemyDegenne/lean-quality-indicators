namespace P2MW.S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise

namespace TOLD0b

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix IntermediateField HahnSeries

section MatrixData

variable {M p : ℕ}

variable {y w₀ : ℤ} (hrel : (p : ℤ) * w₀ - (M : ℤ) * y = 1)
  {γ : SL(2, ℤ)} (hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y; (M : ℤ), (p : ℤ) * w₀])

variable (hp : p ≠ 0)

def scal (p : ℕ) : GL (Fin 2) ℝ := ModularForm.heckeDiagMatrix p * ModularForm.heckeMatrix p 0

end MatrixData
end TOLD0b
end
end P2MW.S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p
