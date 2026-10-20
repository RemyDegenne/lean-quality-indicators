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

protected theorem subsingleton_iff : Subsingleton S ↔ 0 ∈ M :=
  (toLocalizationMap M S).subsingleton_iff

end IsLocalization
end IsLocalization
end CommSemiring
end
