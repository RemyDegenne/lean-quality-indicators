namespace P2MW.S_NumberField_InfiniteAdeleRing_exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

open scoped SchwartzMap ContDiff ComplexConjugate Classical

open NumberField NumberField.InfinitePlace

namespace R4Joint

section Coord

variable (F : Type) [Field F] [NumberField F]

def coordInv (f : Idx F → ℝ) : E2 F := fun i =>
  (fun w => f (i, Sum.inl w), fun w => ⟨f (i, Sum.inr (Sum.inl w)), f (i, Sum.inr (Sum.inr w))⟩)

end Coord
end R4Joint
end
end P2MW.S_NumberField_InfiniteAdeleRing_exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian
