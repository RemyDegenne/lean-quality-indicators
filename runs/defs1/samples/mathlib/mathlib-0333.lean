@[expose] public section

universe u u' v w

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

namespace Matrix

@[inherit_doc]
scoped postfix:1024 "ᴴ" => Matrix.conjTranspose

section ConjTranspose

open Matrix

variable (m n α)

variable {m n α}

variable (m n R α)

/-- `Matrix.conjTranspose` as a `LinearMap` -/
@[simps apply]
def conjTransposeLinearEquiv [CommSemiring R] [StarRing R] [AddCommMonoid α] [StarAddMonoid α]
    [Module R α] [StarModule R α] : Matrix m n α ≃ₗ⋆[R] Matrix n m α where
  __ := conjTransposeAddEquiv m n α
  map_smul' := conjTranspose_smul

end ConjTranspose
end Matrix
end
