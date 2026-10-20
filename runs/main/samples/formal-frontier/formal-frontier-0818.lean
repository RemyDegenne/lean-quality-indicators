set_option warningAsError true

@[expose] public section

namespace Ring

universe u

section AddCommGroup

variable (R : Type u) [AddCommGroup R] [Mul R]

@[simp] theorem additiveCommutatorQuotientOpEquiv_symm_mk (r : Rᵐᵒᵖ) :
    (additiveCommutatorQuotientOpEquiv R).symm (QuotientAddGroup.mk r) =
      QuotientAddGroup.mk (MulOpposite.unop r) :=
  rfl

end AddCommGroup
end Ring
end
