public section

namespace TauCeti

open MulOpposite

open scoped TensorProduct

variable (k A M N : Type*) [CommRing k] [Semiring A]
  [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module A N]

namespace BalancedTensorProduct

variable {M N}

/-- A pure tensor in the balanced tensor product. -/
def tmul (m : M) (n : N) : BalancedTensorProduct k A M N := mk k A m n

end BalancedTensorProduct
end TauCeti
end
