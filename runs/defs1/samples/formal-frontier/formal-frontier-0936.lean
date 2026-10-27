@[expose] public section

universe uR uM uN uA

namespace BalancedTensorProduct

variable {R : Type uR} {M : Type uM} {N : Type uN}

variable [Ring R] [AddCommGroup M] [AddCommGroup N]

variable [Module Rᵐᵒᵖ M] [Module R N]

@[inherit_doc] scoped notation:100 m:100 " ⊗ᵇ[" R "] " n:101 => tmul (R := R) m n

namespace BalancedMap

variable {A : Type uA} [AddCommGroup A]

/-- The homomorphism from the free additive group induced by a balanced map.
This is an implementation detail of `BalancedTensorProduct.lift`. -/
def freeLift (b : BalancedMap (R := R) (M := M) (N := N) A) : Free M N →+ A :=
  FreeAbelianGroup.lift fun mn => b mn.1 mn.2

end BalancedMap
end BalancedTensorProduct
end
