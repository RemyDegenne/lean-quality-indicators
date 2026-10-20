@[expose] public section

variable {R : Type*}

namespace Unitary

section Monoid

variable [Monoid R] [StarMul R]

/-- The unitary elements embed into the units. -/
@[simps]
def toUnits : unitary R →* Rˣ where
  toFun x := ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl

end Monoid
end Unitary
end
