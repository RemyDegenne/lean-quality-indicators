@[expose] public section

universe uR uM uN uA

namespace BalancedTensorProduct

variable (R : Type uR) (M : Type uM) (N : Type uN)

variable [Ring R] [AddCommGroup M] [AddCommGroup N]

variable [Module Rᵐᵒᵖ M] [Module R N]

/-- The free additive commutative group used in the quotient construction. -/
abbrev Free := FreeAbelianGroup (M × N)

end BalancedTensorProduct
end
