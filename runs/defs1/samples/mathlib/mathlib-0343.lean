@[expose] public section

variable {R : Type*} [CommSemiring R] {S : Submonoid R} {M : Type*} [AddCommMonoid M]
  [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')

namespace IsLocalizedModule

variable (S)

variable [IsLocalizedModule S f]

/-- The finset of numerators after clearing the denominators of a finite set of fractions. -/
noncomputable def finsetIntegerMultiple [DecidableEq M] (s : Finset M') : Finset M :=
  s.attach.image fun t => integerMultiple S f s id t

end IsLocalizedModule
end
