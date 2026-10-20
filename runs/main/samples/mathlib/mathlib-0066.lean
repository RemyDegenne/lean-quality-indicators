@[expose] public section

open Function

section CommSemiring

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S]

variable [Algebra R S] {P : Type*} [CommSemiring P]

variable {M}

namespace IsLocalization

section IsLocalization

variable [IsLocalization M S]

variable (M) {S}

variable {M}

variable (M S)

variable {M}

variable {S}

variable (M)

variable {M}

theorem ne_zero_of_mk'_ne_zero {x : R} {y : M} (hxy : IsLocalization.mk' S x y ≠ 0) : x ≠ 0 := by
  rintro rfl
  exact hxy (IsLocalization.mk'_zero _)

end IsLocalization
end IsLocalization
end CommSemiring
end
