@[expose] public section

open Function MulOpposite

variable {α β γ : Type*}

namespace Set

section SMul

/-- The dilation of set `x • s` is defined as `{x • y | y ∈ s}` in scope `Pointwise`. -/
@[to_additive (attr := instance_reducible)
/-- The translation of set `x +ᵥ s` is defined as `{x +ᵥ y | y ∈ s}` in scope `Pointwise`. -/]
protected def smulSet [SMul α β] : SMul α (Set β) where smul a := image (a • ·)

end SMul
end Set
end
