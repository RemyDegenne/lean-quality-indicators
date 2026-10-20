namespace P2MW.S_NumberField_InfiniteAdeleRing_exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

open scoped SchwartzMap ContDiff ComplexConjugate Classical

open NumberField NumberField.InfinitePlace

namespace R4Joint

section Gauss

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (H) in

def gaussSchwartz : 𝓢(H, ℝ) where
  toFun := gauss
  smooth' := contDiff_gauss
  decay' k n := ⟨_, fun z => decay_gauss k n z⟩

end Gauss
end R4Joint
end
end P2MW.S_NumberField_InfiniteAdeleRing_exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian
