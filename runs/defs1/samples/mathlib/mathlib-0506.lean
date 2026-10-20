@[expose] public section

section MulActionHom

variable {M' : Type*}

variable {M : Type*} {N : Type*} {P : Type*}

variable (φ : M → N) (ψ : N → P) (χ : M → P)

variable (X : Type*) [SMul M X] [SMul M' X]

variable (Y : Type*) [SMul N Y] [SMul M' Y]

variable (Z : Type*) [SMul P Z]

/-- Equivariant functions :
When `φ : M → N` is a function, and types `X` and `Y` are endowed with actions of `M` and `N`,
a function `f : X → Y` is `φ`-equivariant if `f (m • x) = (φ m) • (f x)`. -/
@[to_additive]
structure MulActionHom where
  /-- The underlying function. -/
  protected toFun : X → Y
  /-- The proposition that the function commutes with the actions. -/
  protected map_smul' : ∀ (m : M) (x : X), toFun (m • x) = (φ m) • toFun x

end MulActionHom
end
