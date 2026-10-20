@[expose] public section

universe uR uM uN uA

namespace BalancedTensorProduct

variable {R : Type uR} {M : Type uM} {N : Type uN}

variable [Ring R] [AddCommGroup M] [AddCommGroup N]

variable [Module Rᵐᵒᵖ M] [Module R N]

@[inherit_doc] scoped notation:100 m:100 " ⊗ᵇ[" R "] " n:101 => tmul (R := R) m n

section RightAction

universe uS

variable {S : Type uS} [Ring S] [Module Sᵐᵒᵖ N] [SMulCommClass R Sᵐᵒᵖ N]

/-- The action on a balanced tensor product induced by a compatible right
action on the second factor. -/
def smulAddHom (s : Sᵐᵒᵖ) :
    BalancedTensorProduct R M N →+ BalancedTensorProduct R M N :=
  lift (smulBalancedMap (R := R) (M := M) (N := N) s)

end RightAction
end BalancedTensorProduct
end
