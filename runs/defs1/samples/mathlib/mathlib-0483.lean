@[expose] public section

open Function

variable {F α β γ δ : Type*}

infixr:25 " →+o " => OrderAddMonoidHom

infixr:25 " ≃+o " => OrderAddMonoidIso

infixr:25 " →*o " => OrderMonoidHom

infixr:25 " ≃*o " => OrderMonoidIso

namespace OrderMonoidHom

section OrderedCommGroup

variable {_ : CommGroup α} {_ : Preorder α} {_ : CommGroup β} {_ : PartialOrder β}

/-- Makes an ordered group homomorphism from a proof that the map preserves multiplication. -/
@[to_additive
      /-- Makes an ordered additive group homomorphism from a proof that the map preserves
      addition. -/]
def mk' (f : α → β) (hf : Monotone f) (map_mul : ∀ a b : α, f (a * b) = f a * f b) : α →*o β :=
  { MonoidHom.mk' f map_mul with monotone' := hf }

end OrderedCommGroup
end OrderMonoidHom
end
