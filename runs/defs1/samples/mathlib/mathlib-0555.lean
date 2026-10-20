@[expose] public section

open nonZeroDivisors

variable (R : Type*) [CommRing R] {M : Submonoid R} (S : Type*) [CommRing S]

variable [Algebra R S] {P : Type*} [CommRing P]

variable {A : Type*} [CommRing A] (K : Type*)

namespace IsFractionRing

open IsLocalization

variable {R K}

variable {B : Type*} [CommRing B] [IsDomain B] [Field K] {L : Type*} [Field L] [Algebra A K]
  [IsFractionRing A K] {g : A →+* L}

open Function

section ringEquivOfRingEquiv

variable {A K B L : Type*} [CommRing A] [CommRing B] [CommRing K] [CommRing L]
  [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
  (h : A ≃+* B)

/-- Given rings `A, B` and localization maps to their fraction rings
`f : A →+* K, g : B →+* L`, an isomorphism `h : A ≃+* B` induces an isomorphism of
fraction rings `K ≃+* L`. -/
@[simps! apply]
noncomputable def ringEquivOfRingEquiv : K ≃+* L :=
  IsLocalization.ringEquivOfRingEquiv K L h (MulEquivClass.map_nonZeroDivisors h)

end ringEquivOfRingEquiv
end IsFractionRing
end
