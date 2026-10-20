@[expose] public section

open OrderDual

variable (α β : Type*)

section Defs

variable [SMul α β] [Preorder α] [Preorder β]

section Left

variable [Zero α]

/-- Typeclass for strict reverse monotonicity of scalar multiplication by nonnegative elements on
the left, namely `a • b₁ < a • b₂ → b₁ < b₂` if `0 ≤ a`.

You should usually not use this very granular typeclass directly, but rather a typeclass like
`IsOrderedModule`. -/
class PosSMulReflectLT : Prop where
  /-- Do not use this. Use `lt_of_smul_lt_smul_left` instead. -/
  protected lt_of_smul_lt_smul_left ⦃a : α⦄ (ha : 0 ≤ a) ⦃b₁ b₂ : β⦄ (hb : a • b₁ < a • b₂) :
    b₁ < b₂

end Left
end Defs
end
