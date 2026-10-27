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

/-- Localizing at a submonoid with 0 inside it leads to the trivial ring. -/
@[instance_reducible]
def uniqueOfZeroMem (h : (0 : R) ∈ M) : Unique S :=
  uniqueOfZeroEqOne <| by simpa using IsLocalization.map_units S ⟨0, h⟩

end IsLocalization
end IsLocalization
end CommSemiring
end
