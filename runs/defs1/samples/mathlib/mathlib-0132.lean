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

variable {φ X Y}

variable {F : Type*} [FunLike F X Y]

/-- Two equal maps on scalars give rise to an equivariant map for identity -/
@[to_additive /-- Two equal maps on scalars give rise to an equivariant map for identity -/]
def ofEq {φ' : M → N} (h : φ = φ') (f : X →ₑ[φ] Y) : X →ₑ[φ'] Y where
  toFun := f.toFun
  map_smul' m a := h ▸ f.map_smul' m a

end MulActionHom
end MulActionHom
end
