@[expose] public section

variable {ι : Sort*} {M : Type*} [MulOneClass M]

namespace Submonoid

/-- A submonoid `H` of `M` determines a submonoid `H.op` of the opposite monoid `Mᵐᵒᵖ`. -/
@[to_additive (attr := simps) /-- An additive submonoid `H` of `M` determines an additive submonoid
`H.op` of the opposite monoid `Mᵐᵒᵖ`. -/]
def opEquiv : Submonoid M ≃o Submonoid Mᵐᵒᵖ where
  toFun := Submonoid.op
  invFun := Submonoid.unop
  left_inv := unop_op
  right_inv := op_unop
  map_rel_iff' := op_le_op_iff

end Submonoid
end
