@[expose] public section

variable {G₀ : Type*} [GroupWithZero G₀]

namespace OrderIso

variable [PartialOrder G₀]

attribute [local instance] MulPosReflectLT.toMulPosStrictMono MulPosReflectLT.toMulPosReflectLE

section right

variable [MulPosReflectLT G₀]

/-- `Equiv.divRight₀` as an order isomorphism. -/
@[simps! +simpRhs]
def divRight₀ (a : G₀) (ha : 0 < a) : G₀ ≃o G₀ where
  toEquiv := .divRight₀ a ha.ne'
  map_rel_iff' {b c} := by
    simp only [Equiv.divRight₀_apply, div_eq_mul_inv]
    exact mul_le_mul_iff_left₀ (a := a⁻¹) (Right.inv_pos.mpr ha)

end right
end OrderIso
end
