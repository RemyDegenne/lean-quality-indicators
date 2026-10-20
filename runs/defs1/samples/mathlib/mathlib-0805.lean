open scoped Finset

@[expose] public section

variable {R : Type*} [CommSemiring R] {M : Submonoid R} {S : Type*} [CommSemiring S]

variable [Algebra R S]

open Function

namespace IsLocalization

section

variable (R)

/-- Given `a : S`, `S` a localization of `R`, `IsInteger R a` iff `a` is in the image of
the localization map from `R` to `S`. -/
def IsInteger (a : S) : Prop :=
  a ∈ (algebraMap R S).rangeS

end
end IsLocalization
end
