@[expose] public section

open List Set

open scoped Computability

universe v

variable {α β γ : Type*}

namespace Language

variable {l m : Language α} {a b x : List α}

variable (α) in
/-- `Language.reverse` as a ring isomorphism to the opposite ring. -/
@[simps]
def reverseIso : Language α ≃+* (Language α)ᵐᵒᵖ where
  toFun l := .op l.reverse
  invFun l' := l'.unop.reverse
  left_inv := reverse_reverse
  right_inv l' := MulOpposite.unop_injective <| reverse_reverse l'.unop
  map_mul' l₁ l₂ := MulOpposite.unop_injective <| reverse_mul l₁ l₂
  map_add' l₁ l₂ := MulOpposite.unop_injective <| reverse_add l₁ l₂

end Language
end
