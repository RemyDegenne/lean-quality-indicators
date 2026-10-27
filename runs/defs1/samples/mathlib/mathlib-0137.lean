@[expose] public section

variable {R : Type*}

namespace AddMonoidHom

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R]

/-- The multiplication `(x * y) * z` of three elements of a (non-associative)
(semi)-ring is an `AddMonoidHom` in each argument. See also `LinearMap.mulLeftRight` for a
related functions realized as a linear map. -/
def mulLeft₃ : R →+ R →+ R →+ R where
  toFun x := comp mul (mulLeft x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [add_mul]

end NonUnitalNonAssocSemiring
end AddMonoidHom
end
