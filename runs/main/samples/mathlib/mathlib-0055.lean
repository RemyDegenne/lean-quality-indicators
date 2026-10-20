@[expose] public section

universe u u' v v' w w'

namespace NonUnitalSubalgebra

open NonUnitalAlgebra

section NonAssoc

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A]

variable (S : NonUnitalSubalgebra R A)

variable [NonUnitalNonAssocSemiring B] [Module R B]

section Prod

variable (S₁ : NonUnitalSubalgebra R B)

@[simp, norm_cast]
theorem coe_prod : (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ S₁ :=
  rfl

end Prod
end NonAssoc
end NonUnitalSubalgebra
end
