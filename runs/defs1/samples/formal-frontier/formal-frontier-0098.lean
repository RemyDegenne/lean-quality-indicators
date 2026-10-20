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

/-- The balanced map used to define a compatible right action on the tensor
product. This is an implementation detail of `BalancedTensorProduct.smulAddHom`. -/
def smulBalancedMap (s : Sᵐᵒᵖ) :
    BalancedMap (R := R) (M := M) (N := N) (BalancedTensorProduct R M N) where
  toFun m n := m ⊗ᵇ[R] (s • n)
  map_zero_left n := zero_tmul _
  map_add_left m₁ m₂ n := add_tmul _ _ _
  map_zero_right m := by simp
  map_add_right m n₁ n₂ := by rw [smul_add, tmul_add]
  balance r m n := by rw [smul_tmul, smul_comm]

end RightAction
end BalancedTensorProduct
end
