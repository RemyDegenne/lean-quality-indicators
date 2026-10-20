@[expose] public section

universe u v

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

open Function LinearMap

namespace LinearMap

section AddCommMonoid

section SMulRight

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₁] [Module R M] [Module R M₁]

variable [Semiring S] [Module R S] [Module S M] [IsScalarTower R S M]

/-- When `f` is an `R`-linear map taking values in `S`, then `fun b ↦ f b • x` is an `R`-linear
map. -/
def smulRight (f : M₁ →ₗ[R] S) (x : M) : M₁ →ₗ[R] M where
  toFun b := f b • x
  map_add' x y := by rw [f.map_add, add_smul]
  map_smul' b y := by rw [RingHom.id_apply, map_smul, smul_assoc]

end SMulRight
end AddCommMonoid
end LinearMap
end
