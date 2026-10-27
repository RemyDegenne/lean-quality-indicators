namespace P2MW.S_ModPForms_finiteDimensional_modPMod

set_option autoImplicit false

open UpperHalfPlane

open scoped MatrixGroups

namespace RedRank

section QCoeff

variable {N : ℕ} {k : ℤ}

local notation "Γ₀(" N ")" => Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)

noncomputable def coeffL (N : ℕ) (k : ℤ) (n : ℕ) : ModularForm Γ₀(N) k →ₗ[ℂ] ℂ where
  toFun f := ModularFormClass.qCoeff (⇑f) n
  map_add' f g := qCoeff_add f g n
  map_smul' c f := qCoeff_smul c f n

end QCoeff
end RedRank
end P2MW.S_ModPForms_finiteDimensional_modPMod
