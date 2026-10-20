namespace P2MW.S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

namespace R1CuspDeriv

open MeasureTheory Filter Metric Topology

open IsDedekindDomain NumberField AutomorphicForm

open LanglandsTunnell.CubicInduction

section Arch

variable {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}

theorem hasDerivAt_comp_L (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3)
    {s : ℝ} (hs : |s| < 1) :
    HasDerivAt (fun σ => Φ (h * L i j σ)) ((kap i j s : ℂ)⁻¹ * WhittakerBlock.archDeriv i j Φ (h * L i j s)) s := by
  have hk : (kap i j s : ℂ) ≠ 0 := by exact_mod_cast (kap_pos i j hs).ne'
  rw [archDeriv_apply_mul_L hΦ h i j hs, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]
  exact (differentiableAt_comp_L hΦ h i j hs).hasDerivAt

end Arch
end R1CuspDeriv
end
end P2MW.S_LanglandsTunnell_CubicInduction_doubleSlotCoeff_upperTriangular_equivariant_of_joint_expansion_top
