@[expose] public section

section MulActionHom

variable {M' : Type*}

variable {M : Type*} {N : Type*} {P : Type*}

variable (φ : M → N) (ψ : N → P) (χ : M → P)

variable (X : Type*) [SMul M X] [SMul M' X]

variable (Y : Type*) [SMul N Y] [SMul M' Y]

variable (Z : Type*) [SMul P Z]

notation:25 (name := «MulActionHomLocal≺») X " →ₑ[" φ:25 "] " Y:0 => MulActionHom φ X Y

notation:25 (name := «MulActionHomIdLocal≺») X " →[" M:25 "] " Y:0 => MulActionHom (@id M) X Y

notation:25 (name := «AddActionHomLocal≺») X " →ₑ[" φ:25 "] " Y:0 => AddActionHom φ X Y

notation:25 (name := «AddActionHomIdLocal≺») X " →[" M:25 "] " Y:0 => AddActionHom (@id M) X Y

export MulActionSemiHomClass (map_smulₛₗ)

export AddActionSemiHomClass (map_vaddₛₗ)

namespace MulActionHom

open MulActionHom

variable {φ ψ χ X Y Z}

variable {φ' : N → M}

variable {Y₁ : Type*} [SMul M Y₁]

/-- If actions of `M` and `N` on `α` commute,
  then for `c : M`, `(c • · : α → α)` is an `N`-action homomorphism. -/
@[to_additive (attr := simps) /-- If additive actions of `M` and `N` on `α` commute,
  then for `c : M`, `(c • · : α → α)` is an `N`-additive action homomorphism. -/]
def _root_.SMulCommClass.toMulActionHom {M} (N α : Type*)
    [SMul M α] [SMul N α] [SMulCommClass M N α] (c : M) :
    α →[N] α where
  toFun := (c • ·)
  map_smul' := smul_comm _

end MulActionHom
end MulActionHom
end
