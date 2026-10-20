@[expose] public section

open Function

variable {F α β M M₁ M₂ M₃ N N₁ N₂ N₃ P Q G : Type*}

variable [EquivLike F α β]

namespace MulEquiv

section monoidHomCongr

variable [MulOneClass M] [MulOneClass M₁] [MulOneClass M₂] [MulOneClass M₃]
  [CommMonoid N] [CommMonoid N₁] [CommMonoid N₂] [CommMonoid N₃]

/-- The isomorphism `(M₁ →* N) ≃* (M₂ →* N)` obtained by postcomposition with
a multiplicative equivalence `e : M₁ ≃* M₂`. -/
@[to_additive (attr := simps! apply)
/-- The isomorphism `(M₁ →+ N) ≃+ (M₂ →+ N)` obtained by postcomposition with
an additive equivalence `e : M₁ ≃+ M₂`. -/]
def monoidHomCongrLeft (e : M₁ ≃* M₂) : (M₁ →* N) ≃* (M₂ →* N) where
  __ := e.monoidHomCongrLeftEquiv
  map_mul' f g := by ext; simp

end monoidHomCongr
end MulEquiv
end
