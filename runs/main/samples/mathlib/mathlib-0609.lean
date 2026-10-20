@[expose] public section

universe u v w w₁ w₂

section LieSubmodule

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

namespace LieSubmodule

variable {R L M}

variable (N N' : LieSubmodule R L M)

@[simp, norm_cast]
theorem coe_neg (m : N) : (↑(-m) : M) = -(m : M) :=
  rfl

end LieSubmodule
end LieSubmodule
end
