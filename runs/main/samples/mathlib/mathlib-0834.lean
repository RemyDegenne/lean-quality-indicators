@[expose] public section

universe u v w

local notation "tsze" => TrivSqZeroExt

open scoped RightActions

namespace TrivSqZeroExt

open MulOpposite

section Additive

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

section

variable (R)

@[simp]
theorem inr_add [AddZeroClass R] [Add M] (m₁ m₂ : M) :
    (inr (m₁ + m₂) : tsze R M) = inr m₁ + inr m₂ :=
  ext (add_zero 0).symm rfl

end
end Additive
end TrivSqZeroExt
end
